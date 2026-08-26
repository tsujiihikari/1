import org.objectweb.asm.AnnotationVisitor;
import org.objectweb.asm.ClassReader;
import org.objectweb.asm.ClassVisitor;
import org.objectweb.asm.ConstantDynamic;
import org.objectweb.asm.FieldVisitor;
import org.objectweb.asm.Handle;
import org.objectweb.asm.Label;
import org.objectweb.asm.MethodVisitor;
import org.objectweb.asm.Opcodes;
import org.objectweb.asm.Type;
import org.objectweb.asm.TypePath;
import org.objectweb.asm.signature.SignatureReader;
import org.objectweb.asm.signature.SignatureVisitor;

import java.io.BufferedWriter;
import java.io.Closeable;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStreamWriter;
import java.nio.charset.StandardCharsets;
import java.nio.file.FileVisitResult;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.nio.file.SimpleFileVisitor;
import java.nio.file.attribute.BasicFileAttributes;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Set;
import java.util.jar.JarEntry;
import java.util.jar.JarFile;

/**
 * JAR/Class dependency analyzer using ASM.
 *
 * Java source/runtime target: Java 8+
 * Dependency: ASM 9.x core (asm-9.x.jar only)
 *
 * Usage:
 *   javac -cp asm-9.x.jar Main.java
 *   java  -Xmx2048m -cp .:asm-9.x.jar Main [scanRoot] [outputDir]
 *
 * Windows classpath separator:
 *   java -cp .;asm-9.x.jar Main [scanRoot] [outputDir]
 *
 * Output files:
 *   class_def.csv
 *   method_def.csv
 *   class_ref.csv
 *   method_call.csv
 */
public class Main {

    private static final int ASM_API = Opcodes.ASM9;

    /** Per-class uncompressed byte limit. Prevents an abnormal/zip-bomb entry from consuming unlimited heap. */
    private static final int MAX_CLASS_BYTES = Integer.getInteger("asm.maxClassBytes", 32 * 1024 * 1024);

    /** Bounded resolver cache: speeds up repeated calls without unbounded heap growth. */
    private static final int METHOD_RESOLVE_CACHE_SIZE =
            Integer.getInteger("asm.methodResolveCacheSize", 50000);

    private static final String RESOLVED = "RESOLVED";
    private static final String AMBIGUOUS = "AMBIGUOUS_DUPLICATE_CLASS";
    private static final String AMBIGUOUS_HIERARCHY = "AMBIGUOUS_METHOD_HIERARCHY";
    private static final String NOT_FOUND_IN_GROUP = "NOT_FOUND_IN_GROUP";
    private static final String JDK = "JDK";
    private static final String EXTERNAL = "EXTERNAL_NOT_FOUND";
    private static final String HIERARCHY_LIMIT = "HIERARCHY_DEPTH_LIMIT";
    private static final int MAX_HIERARCHY_DEPTH = 256;

    private static final Set<String> JDK_PREFIXES = new HashSet<String>(Arrays.asList(
            "java.", "javax.", "jdk.", "sun.", "com.sun.", "org.w3c.", "org.xml.", "org.ietf."
    ));

    public static void main(String[] args) throws Exception {
        Path scanRoot = args.length >= 1
                ? Paths.get(args[0]).toAbsolutePath().normalize()
                : findScanRoot();

        Path outputDir = args.length >= 2
                ? Paths.get(args[1]).toAbsolutePath().normalize()
                : Paths.get("asm-output").toAbsolutePath().normalize();

        if (!Files.isDirectory(scanRoot)) {
            throw new IllegalArgumentException("scanRoot is not a directory: " + scanRoot);
        }
        if (MAX_CLASS_BYTES < 1024) {
            throw new IllegalArgumentException("asm.maxClassBytes is too small: " + MAX_CLASS_BYTES);
        }
        if (METHOD_RESOLVE_CACHE_SIZE < 0) {
            throw new IllegalArgumentException(
                    "asm.methodResolveCacheSize must be >= 0: " + METHOD_RESOLVE_CACHE_SIZE);
        }

        Files.createDirectories(outputDir);

        System.out.println("SCAN_ROOT=" + normalize(scanRoot.toString()));
        System.out.println("OUTPUT_DIR=" + normalize(outputDir.toString()));
        System.out.println("MAX_CLASS_BYTES=" + MAX_CLASS_BYTES);
        System.out.println("METHOD_RESOLVE_CACHE_SIZE=" + METHOD_RESOLVE_CACHE_SIZE);

        List<JarInfo> jars = discoverJars(scanRoot, outputDir);
        Collections.sort(jars);
        if (jars.isEmpty()) {
            throw new IllegalStateException("No .jar files found under: " + scanRoot);
        }

        System.out.println("JAR_COUNT=" + jars.size());

        Stats stats = new Stats();
        List<GroupWork> groups = groupJars(jars);
        System.out.println("GROUP_COUNT=" + groups.size());
        System.out.println("MAX_HEAP_MB="
                + (Runtime.getRuntime().maxMemory() / (1024L * 1024L)));

        try (CsvOutputs out = new CsvOutputs(outputDir, stats)) {
            // IMPORTANT: process one directory group at a time. The index and resolver cache
            // are discarded before moving to the next group, so heap usage is bounded by the
            // largest single group rather than by all classes below IKO/Master.
            for (int i = 0; i < groups.size(); i++) {
                GroupWork group = groups.get(i);
                System.out.println("[GROUP " + (i + 1) + "/" + groups.size() + "] "
                        + group.group + " JARS=" + group.jars.size());
                processGroup(group, out, stats);
            }
        }

        System.out.println("DONE");
        System.out.println("CLASS_DEF_ROWS=" + stats.classDefRows);
        System.out.println("METHOD_DEF_ROWS=" + stats.methodDefRows);
        System.out.println("CLASS_REF_ROWS=" + stats.classRefRows);
        System.out.println("METHOD_CALL_ROWS=" + stats.methodCallRows);
        System.out.println("SKIPPED_CLASS_ENTRIES=" + stats.skippedClassEntries);
    }

    // ---------------------------------------------------------------------
    // Root/JAR discovery
    // ---------------------------------------------------------------------

    private static Path findScanRoot() throws IOException {
        Path cwd = Paths.get("").toAbsolutePath().normalize();
        LinkedHashSet<Path> candidates = new LinkedHashSet<Path>();

        Path p = cwd;
        while (p != null) {
            candidates.add(p.resolve("IKO").resolve("Master").normalize());
            Path fileName = p.getFileName();
            Path parent = p.getParent();
            if (fileName != null && parent != null && "Master".equals(fileName.toString())) {
                Path parentName = parent.getFileName();
                if (parentName != null && "IKO".equals(parentName.toString())) {
                    candidates.add(p);
                }
            }
            p = p.getParent();
        }

        candidates.add(cwd.resolve("Master").normalize());
        candidates.add(cwd);

        for (Path candidate : candidates) {
            if (Files.isDirectory(candidate) && containsJar(candidate)) {
                return candidate.toAbsolutePath().normalize();
            }
        }

        throw new IllegalStateException(
                "Could not auto-detect IKO/Master or another directory containing JARs. "
                        + "Pass scanRoot as the first argument. cwd=" + cwd);
    }

    private static boolean containsJar(Path root) throws IOException {
        final boolean[] found = new boolean[]{false};
        Files.walkFileTree(root, new SimpleFileVisitor<Path>() {
            @Override
            public FileVisitResult visitFile(Path file, BasicFileAttributes attrs) {
                if (attrs.isRegularFile() && isJar(file)) {
                    found[0] = true;
                    return FileVisitResult.TERMINATE;
                }
                return FileVisitResult.CONTINUE;
            }
        });
        return found[0];
    }

    private static List<JarInfo> discoverJars(final Path scanRoot, final Path outputDir) throws IOException {
        final List<JarInfo> jars = new ArrayList<JarInfo>();
        final Path root = scanRoot.toAbsolutePath().normalize();
        final Path out = outputDir.toAbsolutePath().normalize();
        final boolean outputInsideRoot = out.startsWith(root);

        Files.walkFileTree(scanRoot, new SimpleFileVisitor<Path>() {
            @Override
            public FileVisitResult preVisitDirectory(Path dir, BasicFileAttributes attrs) {
                Path n = dir.toAbsolutePath().normalize();
                if (outputInsideRoot && !out.equals(root)
                        && (n.equals(out) || n.startsWith(out))) {
                    return FileVisitResult.SKIP_SUBTREE;
                }
                return FileVisitResult.CONTINUE;
            }

            @Override
            public FileVisitResult visitFile(Path file, BasicFileAttributes attrs) {
                if (attrs.isRegularFile() && isJar(file)) {
                    jars.add(new JarInfo(scanRoot, file));
                }
                return FileVisitResult.CONTINUE;
            }
        });
        return jars;
    }

    private static boolean isJar(Path path) {
        return Files.isRegularFile(path)
                && path.getFileName().toString().toLowerCase(Locale.ROOT).endsWith(".jar");
    }

    /**
     * Group is the application directory above helper directories such as jar/lib.
     * Examples with scanRoot=IKO/Master:
     *   nikkoEZ/ez.web.online/jar/app.jar           -> nikkoEZ/ez.web.online
     *   nkCCIS/tsnodryak.online.jar/lib/common.jar -> nkCCIS/tsnodryak.online.jar
     */
    private static String determineGroup(Path scanRoot, Path jarPath) {
        Path parent = jarPath.getParent();
        if (parent == null) {
            return ".";
        }

        // Primary rule from the requirements: the directory group is the *.online or
        // *.online.jar directory (for example nikkoEZ/ez.web.online or
        // nkCCIS/tsnodryak.online.jar). Search this BEFORE jar/lib helper directories so
        // deeper nested lib directories can never split one logical directory group.
        Path cursor = parent;
        while (cursor != null && cursor.startsWith(scanRoot)) {
            String lower = fileName(cursor).toLowerCase(Locale.ROOT);
            if (lower.endsWith(".online") || lower.endsWith(".online.jar")) {
                return relative(scanRoot, cursor);
            }
            if (cursor.equals(scanRoot)) {
                break;
            }
            cursor = cursor.getParent();
        }

        // Fallback for reduced test trees whose directory names do not follow the real
        // *.online naming convention. The directory immediately above a jar/lib helper
        // directory is treated as the group.
        cursor = parent;
        while (cursor != null && cursor.startsWith(scanRoot)) {
            String name = fileName(cursor);
            if (isHelperDir(name)) {
                Path groupDir = cursor;
                while (groupDir != null && groupDir.startsWith(scanRoot)
                        && isHelperDir(fileName(groupDir))) {
                    groupDir = groupDir.getParent();
                }
                if (groupDir != null && groupDir.startsWith(scanRoot)) {
                    return relative(scanRoot, groupDir);
                }
            }
            if (cursor.equals(scanRoot)) {
                break;
            }
            cursor = cursor.getParent();
        }

        // Reduced test trees: all JARs immediately under the selected root can share one group.
        if (parent.equals(scanRoot)) {
            return ".";
        }
        return relative(scanRoot, parent);
    }

    private static boolean isHelperDir(String name) {
        return "jar".equalsIgnoreCase(name) || "lib".equalsIgnoreCase(name);
    }

    private static String fileName(Path path) {
        Path n = path == null ? null : path.getFileName();
        return n == null ? "" : n.toString();
    }

    private static String relative(Path root, Path path) {
        try {
            String s = normalize(root.relativize(path).toString());
            return s.length() == 0 ? "." : s;
        } catch (RuntimeException e) {
            return normalize(path.toString());
        }
    }

    private static List<GroupWork> groupJars(List<JarInfo> jars) {
        // jars are already sorted by group/path. LinkedHashMap preserves that order.
        Map<String, List<JarInfo>> byGroup = new LinkedHashMap<String, List<JarInfo>>();
        for (JarInfo jar : jars) {
            List<JarInfo> list = byGroup.get(jar.group);
            if (list == null) {
                list = new ArrayList<JarInfo>();
                byGroup.put(jar.group, list);
            }
            list.add(jar);
        }

        List<GroupWork> result = new ArrayList<GroupWork>(byGroup.size());
        for (Map.Entry<String, List<JarInfo>> e : byGroup.entrySet()) {
            result.add(new GroupWork(e.getKey(), e.getValue()));
        }
        return result;
    }

    /**
     * All large, group-specific data is local to this method. Once it returns, the entire
     * class/method index and the bounded resolver cache become garbage-collectable.
     */
    private static void processGroup(GroupWork group, CsvOutputs out, Stats stats) {
        Index index = new Index();

        // PASS 1: index only this directory group and emit definition rows immediately.
        for (int i = 0; i < group.jars.size(); i++) {
            JarInfo jar = group.jars.get(i);
            System.out.println("  [INDEX " + (i + 1) + "/" + group.jars.size() + "] "
                    + jar.relativePath);
            indexJar(jar, index, out, stats);
        }

        MethodResolver resolver = new MethodResolver(index);

        // PASS 2: resolve references/calls only against this group's index.
        for (int i = 0; i < group.jars.size(); i++) {
            JarInfo jar = group.jars.get(i);
            System.out.println("  [ANALYZE " + (i + 1) + "/" + group.jars.size() + "] "
                    + jar.relativePath);
            analyzeJar(jar, index, resolver, out, stats);
        }
    }

    // ---------------------------------------------------------------------
    // PASS 1 - definitions/index
    // ---------------------------------------------------------------------

    private static void indexJar(JarInfo jarInfo, Index index, CsvOutputs out, Stats stats) {
        JarFile jar = null;
        try {
            jar = new JarFile(jarInfo.path.toFile(), false);
            java.util.Enumeration<JarEntry> entries = jar.entries();
            while (entries.hasMoreElements()) {
                JarEntry entry = entries.nextElement();
                if (!isClassEntry(entry)) {
                    continue;
                }

                ClassReader cr = readClassReader(jar, entry, jarInfo, stats);
                if (cr == null) {
                    continue;
                }

                DefinitionVisitor visitor = new DefinitionVisitor(jarInfo);
                try {
                    cr.accept(visitor, ClassReader.SKIP_FRAMES);
                } catch (RuntimeException e) {
                    stats.skippedClassEntries++;
                    warn("INDEX_CLASS", jarInfo, entry, e);
                    continue;
                }

                if (visitor.classDef != null) {
                    index.add(visitor.classDef);
                    // CSV failures are deliberately not swallowed as class-parse failures.
                    // Disk-full / permission errors must stop the run instead of producing
                    // silently incomplete analysis files.
                    out.writeClassDef(visitor.classDef);
                    for (MethodDef method : visitor.classDef.methods.values()) {
                        out.writeMethodDef(visitor.classDef, method);
                    }
                }
            }
        } catch (IOException e) {
            warn("INDEX_JAR", jarInfo, null, e);
        } catch (CsvWriteException e) {
            throw e;
        } catch (RuntimeException e) {
            warn("INDEX_JAR", jarInfo, null, e);
        } finally {
            closeQuietly(jar);
        }
    }

    private static final class DefinitionVisitor extends ClassVisitor {
        private final JarInfo jarInfo;
        private ClassDef classDef;

        DefinitionVisitor(JarInfo jarInfo) {
            super(ASM_API);
            this.jarInfo = jarInfo;
        }

        @Override
        public void visit(int version, int access, String name, String signature,
                          String superName, String[] interfaces) {
            ClassDef d = new ClassDef();
            d.group = jarInfo.group;
            d.jarPath = jarInfo.relativePath;
            d.className = internalToClass(name);
            d.access = access;
            d.superClassName = internalToClass(superName);
            if (interfaces != null) {
                for (String intf : interfaces) {
                    d.interfaces.add(internalToClass(intf));
                }
            }
            classDef = d;
        }

        @Override
        public void visitSource(String source, String debug) {
            if (classDef != null) {
                classDef.sourceFile = source;
            }
        }

        @Override
        public MethodVisitor visitMethod(final int access, final String name,
                                         final String descriptor, String signature,
                                         String[] exceptions) {
            if (classDef == null) {
                return null;
            }

            final MethodDef m = new MethodDef();
            m.name = name;
            m.descriptor = descriptor;
            m.access = access;

            final Type[] argumentTypes = safeArgumentTypes(descriptor);
            final int[] parameterSlots = argumentSlots(access, argumentTypes);
            classDef.methods.put(new MethodKey(name, descriptor), m);

            return new MethodVisitor(ASM_API) {
                private int visitParameterIndex = 0;

                @Override
                public void visitParameter(String parameterName, int parameterAccess) {
                    if (visitParameterIndex < argumentTypes.length
                            && parameterName != null && parameterName.length() > 0) {
                        if (m.parameterNames == null) {
                            m.parameterNames = new String[argumentTypes.length];
                        }
                        m.parameterNames[visitParameterIndex] = parameterName;
                    }
                    visitParameterIndex++;
                }

                @Override
                public void visitLocalVariable(String localName, String localDescriptor,
                                               String localSignature, Label start, Label end,
                                               int index) {
                    if (localName == null || localName.length() == 0) {
                        return;
                    }
                    // A later local variable may reuse a parameter slot. Only an LVT entry
                    // whose scope starts at bytecode offset 0 is safe to treat as a parameter.
                    try {
                        if (start == null || start.getOffset() != 0) {
                            return;
                        }
                    } catch (IllegalStateException e) {
                        return;
                    }
                    for (int i = 0; i < parameterSlots.length; i++) {
                        if (parameterSlots[i] == index
                                && localDescriptor != null
                                && localDescriptor.equals(argumentTypes[i].getDescriptor())) {
                            if (m.parameterNames == null) {
                                m.parameterNames = new String[argumentTypes.length];
                            }
                            if (m.parameterNames[i] == null) {
                                m.parameterNames[i] = localName;
                            }
                            break;
                        }
                    }
                }

                @Override
                public void visitLineNumber(int line, Label start) {
                    if (m.firstLine < 0 || line < m.firstLine) {
                        m.firstLine = line;
                    }
                    if (line > m.lastLine) {
                        m.lastLine = line;
                    }
                }
            };
        }
    }

    // ---------------------------------------------------------------------
    // PASS 2 - references/calls
    // ---------------------------------------------------------------------

    private static void analyzeJar(JarInfo jarInfo, Index index, MethodResolver resolver,
                                   CsvOutputs out, Stats stats) {
        JarFile jar = null;
        try {
            jar = new JarFile(jarInfo.path.toFile(), false);
            java.util.Enumeration<JarEntry> entries = jar.entries();
            while (entries.hasMoreElements()) {
                JarEntry entry = entries.nextElement();
                if (!isClassEntry(entry)) {
                    continue;
                }

                ClassReader cr = readClassReader(jar, entry, jarInfo, stats);
                if (cr == null) {
                    continue;
                }

                try {
                    cr.accept(new DependencyVisitor(jarInfo, index, resolver, out),
                            ClassReader.SKIP_FRAMES);
                } catch (CsvWriteException e) {
                    throw e;
                } catch (RuntimeException e) {
                    stats.skippedClassEntries++;
                    warn("ANALYZE_CLASS", jarInfo, entry, e);
                }
            }
        } catch (IOException e) {
            warn("ANALYZE_JAR", jarInfo, null, e);
        } catch (CsvWriteException e) {
            throw e;
        } catch (RuntimeException e) {
            warn("ANALYZE_JAR", jarInfo, null, e);
        } finally {
            closeQuietly(jar);
        }
    }

    private static final class DependencyVisitor extends ClassVisitor {
        private final JarInfo originJar;
        private final Index index;
        private final MethodResolver resolver;
        private final CsvOutputs out;

        private String originClass = "";
        private String sourceFile = "";

        /** One set per class only; discarded after each ClassReader.accept(). */
        private final Set<String> classRefDedupe = new HashSet<String>();

        DependencyVisitor(JarInfo originJar, Index index, MethodResolver resolver, CsvOutputs out) {
            super(ASM_API);
            this.originJar = originJar;
            this.index = index;
            this.resolver = resolver;
            this.out = out;
        }

        @Override
        public void visit(int version, int access, String name, String signature,
                          String superName, String[] interfaces) {
            originClass = internalToClass(name);
            addRef("", -1, "EXTENDS", internalToClass(superName));
            if (interfaces != null) {
                for (String intf : interfaces) {
                    addRef("", -1, "IMPLEMENTS", internalToClass(intf));
                }
            }
            collectClassOrMethodSignature(signature, new RefConsumer("", -1, "CLASS_SIGNATURE"));
        }

        @Override
        public void visitSource(String source, String debug) {
            sourceFile = safe(source);
        }

        @Override
        public void visitOuterClass(String owner, String name, String descriptor) {
            addRef("", -1, "OUTER_CLASS", internalToClass(owner));
            collectDescriptor(descriptor, new RefConsumer("", -1, "OUTER_METHOD_DESCRIPTOR"));
        }

        @Override
        public void visitInnerClass(String name, String outerName, String innerName, int access) {
            addRef("", -1, "INNER_CLASS", internalToClass(name));
            addRef("", -1, "INNER_OUTER_CLASS", internalToClass(outerName));
        }

        @Override
        public AnnotationVisitor visitAnnotation(String descriptor, boolean visible) {
            collectDescriptor(descriptor, new RefConsumer("", -1, "CLASS_ANNOTATION"));
            return new DepAnnotationVisitor("", -1, "CLASS_ANNOTATION_VALUE");
        }

        @Override
        public AnnotationVisitor visitTypeAnnotation(int typeRef, TypePath typePath,
                                                     String descriptor, boolean visible) {
            collectDescriptor(descriptor, new RefConsumer("", -1, "CLASS_TYPE_ANNOTATION"));
            return new DepAnnotationVisitor("", -1, "CLASS_TYPE_ANNOTATION_VALUE");
        }

        @Override
        public FieldVisitor visitField(int access, String name, String descriptor,
                                       String signature, Object value) {
            collectDescriptor(descriptor, new RefConsumer("", -1, "FIELD_TYPE"));
            collectTypeSignature(signature, new RefConsumer("", -1, "FIELD_SIGNATURE"));
            collectConstant(value, new RefConsumer("", -1, "FIELD_CONSTANT"));

            return new FieldVisitor(ASM_API) {
                @Override
                public AnnotationVisitor visitAnnotation(String descriptor, boolean visible) {
                    collectDescriptor(descriptor, new RefConsumer("", -1, "FIELD_ANNOTATION"));
                    return new DepAnnotationVisitor("", -1, "FIELD_ANNOTATION_VALUE");
                }


                @Override
                public AnnotationVisitor visitTypeAnnotation(int typeRef, TypePath typePath,
                                                             String descriptor, boolean visible) {
                    collectDescriptor(descriptor,
                            new RefConsumer("", -1, "FIELD_TYPE_ANNOTATION"));
                    return new DepAnnotationVisitor("", -1,
                            "FIELD_TYPE_ANNOTATION_VALUE");
                }
            };
        }

        @Override
        public MethodVisitor visitMethod(final int access, final String name,
                                         final String descriptor, String signature,
                                         String[] exceptions) {
            final MethodDef indexed = index.findMethodExact(
                    originJar.group, originClass, name, descriptor, originJar.relativePath);
            final String readableOrigin = indexed == null
                    ? readableMethod(originClass, access, name, descriptor, null)
                    : readableMethod(originClass, access, name, descriptor, indexed.parameterNames);

            collectDescriptor(descriptor, new RefConsumer(readableOrigin, -1, "METHOD_DESCRIPTOR"));
            collectClassOrMethodSignature(signature,
                    new RefConsumer(readableOrigin, -1, "METHOD_SIGNATURE"));
            if (exceptions != null) {
                for (String ex : exceptions) {
                    addRef(readableOrigin, -1, "THROWS", internalToClass(ex));
                }
            }

            return new MethodVisitor(ASM_API) {
                private int line = -1;

                @Override
                public void visitLineNumber(int newLine, Label start) {
                    line = newLine;
                }

                @Override
                public void visitTryCatchBlock(Label start, Label end, Label handler, String type) {
                    addRef(readableOrigin, line, "CATCH_TYPE", internalToClass(type));
                }

                @Override
                public AnnotationVisitor visitAnnotation(String desc, boolean visible) {
                    collectDescriptor(desc, new RefConsumer(readableOrigin, line, "METHOD_ANNOTATION"));
                    return new DepAnnotationVisitor(readableOrigin, line, "METHOD_ANNOTATION_VALUE");
                }


                @Override
                public AnnotationVisitor visitTypeAnnotation(int typeRef, TypePath typePath,
                                                             String desc, boolean visible) {
                    collectDescriptor(desc,
                            new RefConsumer(readableOrigin, line, "METHOD_TYPE_ANNOTATION"));
                    return new DepAnnotationVisitor(readableOrigin, line,
                            "METHOD_TYPE_ANNOTATION_VALUE");
                }

                @Override
                public AnnotationVisitor visitInsnAnnotation(int typeRef, TypePath typePath,
                                                             String desc, boolean visible) {
                    collectDescriptor(desc,
                            new RefConsumer(readableOrigin, line, "INSN_TYPE_ANNOTATION"));
                    return new DepAnnotationVisitor(readableOrigin, line,
                            "INSN_TYPE_ANNOTATION_VALUE");
                }

                @Override
                public AnnotationVisitor visitTryCatchAnnotation(int typeRef, TypePath typePath,
                                                                 String desc, boolean visible) {
                    collectDescriptor(desc,
                            new RefConsumer(readableOrigin, line, "TRY_CATCH_TYPE_ANNOTATION"));
                    return new DepAnnotationVisitor(readableOrigin, line,
                            "TRY_CATCH_TYPE_ANNOTATION_VALUE");
                }

                @Override
                public AnnotationVisitor visitLocalVariableAnnotation(
                        int typeRef, TypePath typePath, Label[] start, Label[] end,
                        int[] index, String desc, boolean visible) {
                    collectDescriptor(desc,
                            new RefConsumer(readableOrigin, line, "LOCAL_TYPE_ANNOTATION"));
                    return new DepAnnotationVisitor(readableOrigin, line,
                            "LOCAL_TYPE_ANNOTATION_VALUE");
                }

                @Override
                public AnnotationVisitor visitParameterAnnotation(int parameter, String desc,
                                                                  boolean visible) {
                    collectDescriptor(desc,
                            new RefConsumer(readableOrigin, line, "PARAMETER_ANNOTATION"));
                    return new DepAnnotationVisitor(readableOrigin, line,
                            "PARAMETER_ANNOTATION_VALUE");
                }

                @Override
                public void visitTypeInsn(int opcode, String type) {
                    String kind;
                    switch (opcode) {
                        case Opcodes.NEW: kind = "NEW"; break;
                        case Opcodes.ANEWARRAY: kind = "ANEWARRAY"; break;
                        case Opcodes.CHECKCAST: kind = "CHECKCAST"; break;
                        case Opcodes.INSTANCEOF: kind = "INSTANCEOF"; break;
                        default: kind = "TYPE_INSN"; break;
                    }
                    if (type != null && type.startsWith("[")) {
                        collectDescriptor(type, new RefConsumer(readableOrigin, line, kind));
                    } else {
                        addRef(readableOrigin, line, kind, internalToClass(type));
                    }
                }

                @Override
                public void visitMultiANewArrayInsn(String desc, int dims) {
                    collectDescriptor(desc,
                            new RefConsumer(readableOrigin, line, "MULTIANEWARRAY"));
                }

                @Override
                public void visitFieldInsn(int opcode, String owner, String fieldName,
                                           String fieldDescriptor) {
                    addRef(readableOrigin, line, fieldOpcodeName(opcode), internalToClass(owner));
                    collectDescriptor(fieldDescriptor,
                            new RefConsumer(readableOrigin, line, "FIELD_DESCRIPTOR"));
                }

                @Override
                public void visitMethodInsn(int opcode, String owner, String calledName,
                                            String calledDescriptor, boolean isInterface) {
                    String ownerClass = internalToClass(owner);
                    addRef(readableOrigin, line, methodOpcodeName(opcode), ownerClass);
                    collectDescriptor(calledDescriptor,
                            new RefConsumer(readableOrigin, line, "CALLED_METHOD_DESCRIPTOR"));

                    MethodResolution r = resolver.resolve(
                            originJar.group, ownerClass, calledName, calledDescriptor);
                    out.writeMethodCall(originJar.group, originJar.relativePath,
                            originClass, readableOrigin, sourceFile, line,
                            methodOpcodeName(opcode), ownerClass, calledName, calledDescriptor,
                            readableMethod(ownerClass, 0, calledName, calledDescriptor, null),
                            r, dispatchKind(opcode));
                }

                @Override
                public void visitInvokeDynamicInsn(String invokedName, String invokedDescriptor,
                                                   Handle bootstrapMethodHandle,
                                                   Object... bootstrapMethodArguments) {
                    collectDescriptor(invokedDescriptor,
                            new RefConsumer(readableOrigin, line, "INVOKEDYNAMIC_DESCRIPTOR"));
                    inspectHandle(readableOrigin, line, bootstrapMethodHandle,
                            "BOOTSTRAP_HANDLE", false);
                    if (bootstrapMethodArguments != null) {
                        for (Object arg : bootstrapMethodArguments) {
                            inspectBootstrapArg(readableOrigin, line, arg);
                        }
                    }
                }

                @Override
                public void visitLdcInsn(Object value) {
                    collectConstant(value, new RefConsumer(readableOrigin, line, "LDC_CLASS"));
                    if (value instanceof ConstantDynamic) {
                        inspectConstantDynamic(readableOrigin, line, (ConstantDynamic) value);
                    }
                }

                private void inspectBootstrapArg(String originMethod, int currentLine, Object arg) {
                    if (arg instanceof Handle) {
                        // Lambda/metafactory implementation handles are real bytecode method references.
                        inspectHandle(originMethod, currentLine, (Handle) arg,
                                "BOOTSTRAP_ARG_HANDLE", true);
                    } else if (arg instanceof Type) {
                        collectType((Type) arg,
                                new RefConsumer(originMethod, currentLine, "BOOTSTRAP_TYPE"));
                    } else if (arg instanceof ConstantDynamic) {
                        inspectConstantDynamic(originMethod, currentLine, (ConstantDynamic) arg);
                    }
                }

                private void inspectConstantDynamic(String originMethod, int currentLine,
                                                    ConstantDynamic cd) {
                    if (cd == null) {
                        return;
                    }
                    collectDescriptor(cd.getDescriptor(),
                            new RefConsumer(originMethod, currentLine,
                                    "CONSTANT_DYNAMIC_DESCRIPTOR"));
                    inspectHandle(originMethod, currentLine, cd.getBootstrapMethod(),
                            "CONSTANT_DYNAMIC_BOOTSTRAP", false);
                    for (int i = 0; i < cd.getBootstrapMethodArgumentCount(); i++) {
                        inspectBootstrapArg(originMethod, currentLine,
                                cd.getBootstrapMethodArgument(i));
                    }
                }

                private void inspectHandle(String originMethod, int currentLine, Handle handle,
                                           String kind, boolean emitMethodCall) {
                    if (handle == null) {
                        return;
                    }
                    String ownerClass = internalToClass(handle.getOwner());
                    addRef(originMethod, currentLine, kind, ownerClass);
                    collectDescriptor(handle.getDesc(),
                            new RefConsumer(originMethod, currentLine, kind + "_DESCRIPTOR"));

                    if (emitMethodCall && isMethodHandleTag(handle.getTag())) {
                        MethodResolution r = resolver.resolve(originJar.group, ownerClass,
                                handle.getName(), handle.getDesc());
                        out.writeMethodCall(originJar.group, originJar.relativePath,
                                originClass, originMethod, sourceFile, currentLine,
                                handleTagName(handle.getTag()), ownerClass,
                                handle.getName(), handle.getDesc(),
                                readableMethod(ownerClass, 0, handle.getName(),
                                        handle.getDesc(), null),
                                r, "DYNAMIC_HANDLE");
                    }
                }
            };
        }

        private final class RefConsumer implements TypeConsumer {
            private final String method;
            private final int line;
            private final String kind;

            RefConsumer(String method, int line, String kind) {
                this.method = method;
                this.line = line;
                this.kind = kind;
            }

            @Override
            public void accept(String className) {
                addRef(method, line, kind, className);
            }
        }

        private final class DepAnnotationVisitor extends AnnotationVisitor {
            private final String method;
            private final int line;
            private final String kind;

            DepAnnotationVisitor(String method, int line, String kind) {
                super(ASM_API);
                this.method = method;
                this.line = line;
                this.kind = kind;
            }

            @Override
            public void visit(String name, Object value) {
                collectConstant(value, new RefConsumer(method, line, kind));
            }

            @Override
            public void visitEnum(String name, String descriptor, String value) {
                collectDescriptor(descriptor, new RefConsumer(method, line, kind + "_ENUM"));
            }

            @Override
            public AnnotationVisitor visitAnnotation(String name, String descriptor) {
                collectDescriptor(descriptor, new RefConsumer(method, line, kind + "_NESTED"));
                return new DepAnnotationVisitor(method, line, kind);
            }

            @Override
            public AnnotationVisitor visitArray(String name) {
                return new DepAnnotationVisitor(method, line, kind);
            }
        }

        /**
         * class_ref.csv intentionally deduplicates by origin class + kind + target class.
         * The first observed method/line is kept only as a locator. This prevents row explosion.
         */
        private void addRef(String originMethod, int line, String kind, String targetClass) {
            if (targetClass == null || targetClass.length() == 0 || targetClass.equals(originClass)) {
                return;
            }
            String key = kind + '\u0001' + targetClass;
            if (!classRefDedupe.add(key)) {
                return;
            }
            ClassResolution cr = index.resolveClass(originJar.group, targetClass);
            out.writeClassRef(originJar.group, originJar.relativePath, originClass,
                    safe(originMethod), sourceFile, line, kind, targetClass, cr);
        }
    }

    // ---------------------------------------------------------------------
    // Index/resolution
    // ---------------------------------------------------------------------

    private static final class Index {
        // group -> className -> zero/one/multiple definitions
        private final Map<String, Map<String, List<ClassDef>>> classes =
                new HashMap<String, Map<String, List<ClassDef>>>();

        void add(ClassDef d) {
            Map<String, List<ClassDef>> byClass = classes.get(d.group);
            if (byClass == null) {
                byClass = new HashMap<String, List<ClassDef>>();
                classes.put(d.group, byClass);
            }
            List<ClassDef> defs = byClass.get(d.className);
            if (defs == null) {
                defs = new ArrayList<ClassDef>(1);
                byClass.put(d.className, defs);
            }
            defs.add(d);
        }

        List<ClassDef> find(String group, String className) {
            Map<String, List<ClassDef>> byClass = classes.get(group);
            if (byClass == null) {
                return Collections.emptyList();
            }
            List<ClassDef> defs = byClass.get(className);
            return defs == null ? Collections.<ClassDef>emptyList() : defs;
        }

        MethodDef findMethodExact(String group, String className, String name,
                                  String descriptor, String jarPath) {
            List<ClassDef> defs = find(group, className);
            for (ClassDef d : defs) {
                if (d.jarPath.equals(jarPath)) {
                    return d.methods.get(new MethodKey(name, descriptor));
                }
            }
            return null;
        }

        ClassResolution resolveClass(String group, String className) {
            List<ClassDef> defs = find(group, className);
            if (defs.size() == 1) {
                return ClassResolution.resolved(defs.get(0).jarPath);
            }
            if (defs.size() > 1) {
                List<String> candidates = new ArrayList<String>(defs.size());
                for (ClassDef d : defs) {
                    candidates.add(d.jarPath);
                }
                Collections.sort(candidates);
                return ClassResolution.ambiguous(candidates);
            }
            return ClassResolution.notFound(isJdkClass(className) ? JDK : EXTERNAL);
        }
    }

    private static final class MethodResolver {
        private final Index index;
        private final Map<String, MethodResolution> cache;

        MethodResolver(Index index) {
            this.index = index;
            if (METHOD_RESOLVE_CACHE_SIZE == 0) {
                this.cache = null;
            } else {
                this.cache = new LinkedHashMap<String, MethodResolution>(1024, 0.75f, true) {
                    @Override
                    protected boolean removeEldestEntry(Map.Entry<String, MethodResolution> eldest) {
                        return size() > METHOD_RESOLVE_CACHE_SIZE;
                    }
                };
            }
        }

        MethodResolution resolve(String group, String owner, String name, String descriptor) {
            String cacheKey = group + '\u0001' + safe(owner) + '\u0001'
                    + safe(name) + '\u0001' + safe(descriptor);
            if (cache != null) {
                MethodResolution cached = cache.get(cacheKey);
                if (cached != null) {
                    return cached;
                }
            }

            MethodResolution result = resolveUncached(group, owner, name, descriptor);
            if (cache != null) {
                cache.put(cacheKey, result);
            }
            return result;
        }

        private MethodResolution resolveUncached(String group, String owner, String name,
                                                  String descriptor) {
            if (owner == null || owner.length() == 0) {
                return MethodResolution.notFound(NOT_FOUND_IN_GROUP);
            }

            // Constructors are never inherited.
            if ("<init>".equals(name)) {
                return resolveExactOwner(group, owner, name, descriptor);
            }

            MethodKey key = new MethodKey(name, descriptor);
            List<ClassDef> ownerDefs = index.find(group, owner);
            if (ownerDefs.size() > 1) {
                return ambiguousDuplicateClass(ownerDefs, key);
            }
            if (ownerDefs.isEmpty()) {
                return MethodResolution.notFound(isJdkClass(owner) ? JDK : EXTERNAL);
            }

            // Fast path: most calls resolve on the symbolic owner itself. Avoid allocating
            // hierarchy traversal collections for this overwhelmingly common case.
            ClassDef ownerDef = ownerDefs.get(0);
            MethodDef ownMethod = ownerDef.methods.get(key);
            if (ownMethod != null) {
                return MethodResolution.resolved(ownerDef, ownMethod);
            }

            List<String> interfaceRoots = null;
            if (!ownerDef.interfaces.isEmpty()) {
                interfaceRoots = new ArrayList<String>(ownerDef.interfaces);
            }

            String fallbackStatus = NOT_FOUND_IN_GROUP;
            String current = (ownerDef.access & Opcodes.ACC_INTERFACE) != 0
                    ? "" : ownerDef.superClassName;
            int depth = 0;

            // Valid Java class hierarchies are acyclic. A hard depth bound protects against
            // malformed bytecode without allocating a HashSet for every cache miss.
            while (current != null && current.length() > 0) {
                if (++depth > MAX_HIERARCHY_DEPTH) {
                    return MethodResolution.notFound(HIERARCHY_LIMIT);
                }

                List<ClassDef> defs = index.find(group, current);
                if (defs.size() > 1) {
                    return ambiguousDuplicateClass(defs, key);
                }
                if (defs.isEmpty()) {
                    fallbackStatus = mergeMissingStatus(fallbackStatus, current);
                    break;
                }

                ClassDef d = defs.get(0);
                MethodDef m = d.methods.get(key);
                if (m != null) {
                    return MethodResolution.resolved(d, m);
                }

                if (!d.interfaces.isEmpty()) {
                    if (interfaceRoots == null) {
                        interfaceRoots = new ArrayList<String>();
                    }
                    interfaceRoots.addAll(d.interfaces);
                }

                if ((d.access & Opcodes.ACC_INTERFACE) != 0) {
                    break;
                }
                current = d.superClassName;
            }

            MethodResolution interfaceResult = resolveInterfaces(
                    group, key,
                    interfaceRoots == null ? Collections.<String>emptyList() : interfaceRoots,
                    fallbackStatus);
            if (interfaceResult != null) {
                if ((ownerDef.access & Opcodes.ACC_INTERFACE) != 0
                        && NOT_FOUND_IN_GROUP.equals(interfaceResult.status)
                        && isJava8ObjectPublicInstanceMethod(name, descriptor)) {
                    return MethodResolution.notFound(JDK);
                }
                return interfaceResult;
            }

            if ((ownerDef.access & Opcodes.ACC_INTERFACE) != 0
                    && isJava8ObjectPublicInstanceMethod(name, descriptor)) {
                return MethodResolution.notFound(JDK);
            }
            return MethodResolution.notFound(fallbackStatus);
        }

        private MethodResolution resolveInterfaces(String group, MethodKey key,
                                                   List<String> roots, String fallbackStatus) {
            if (roots.isEmpty()) {
                return null;
            }

            Deque<InterfaceNode> queue = new ArrayDeque<InterfaceNode>();
            Set<String> visited = new HashSet<String>();
            List<InterfaceMethodCandidate> matches =
                    new ArrayList<InterfaceMethodCandidate>();
            String missingStatus = fallbackStatus;

            for (String root : roots) {
                if (root != null && root.length() > 0) {
                    queue.addLast(new InterfaceNode(root, 0));
                }
            }

            while (!queue.isEmpty()) {
                InterfaceNode node = queue.removeFirst();
                if (!visited.add(node.className)) {
                    continue;
                }
                if (node.depth > MAX_HIERARCHY_DEPTH) {
                    return MethodResolution.notFound(HIERARCHY_LIMIT);
                }

                List<ClassDef> defs = index.find(group, node.className);
                if (defs.size() > 1) {
                    return ambiguousDuplicateClass(defs, key);
                }
                if (defs.isEmpty()) {
                    missingStatus = mergeMissingStatus(missingStatus, node.className);
                    continue;
                }

                ClassDef d = defs.get(0);
                MethodDef m = d.methods.get(key);
                if (m != null) {
                    matches.add(new InterfaceMethodCandidate(d, m));
                }

                // Continue into parents even after a declaration is found.
                // JVM interface resolution chooses maximally-specific declarations.
                for (String parent : d.interfaces) {
                    if (parent != null && parent.length() > 0) {
                        queue.addLast(new InterfaceNode(parent, node.depth + 1));
                    }
                }
            }

            if (matches.isEmpty()) {
                return MethodResolution.notFound(missingStatus);
            }

            List<InterfaceMethodCandidate> maximal =
                    new ArrayList<InterfaceMethodCandidate>(matches.size());

            for (int i = 0; i < matches.size(); i++) {
                InterfaceMethodCandidate candidate = matches.get(i);
                boolean shadowed = false;

                for (int j = 0; j < matches.size(); j++) {
                    if (i == j) {
                        continue;
                    }
                    InterfaceMethodCandidate other = matches.get(j);
                    if (isStrictSubInterface(group,
                            other.owner.className, candidate.owner.className)) {
                        shadowed = true;
                        break;
                    }
                }

                if (!shadowed) {
                    maximal.add(candidate);
                }
            }

            if (maximal.size() == 1) {
                InterfaceMethodCandidate c = maximal.get(0);
                return MethodResolution.resolved(c.owner, c.method);
            }

            List<String> candidates = new ArrayList<String>(maximal.size());
            for (InterfaceMethodCandidate c : maximal) {
                candidates.add(c.owner.jarPath + "!" + c.owner.className + "#"
                        + readableMethod(c.owner.className, c.method.access, c.method.name,
                        c.method.descriptor, c.method.parameterNames));
            }
            Collections.sort(candidates);
            return MethodResolution.ambiguous(AMBIGUOUS_HIERARCHY, candidates);
        }

        private boolean isStrictSubInterface(String group, String possibleChild,
                                             String possibleParent) {
            if (possibleChild == null || possibleParent == null
                    || possibleChild.equals(possibleParent)) {
                return false;
            }

            Deque<InterfaceNode> queue = new ArrayDeque<InterfaceNode>();
            Set<String> visited = new HashSet<String>();
            queue.addLast(new InterfaceNode(possibleChild, 0));

            while (!queue.isEmpty()) {
                InterfaceNode node = queue.removeFirst();
                if (!visited.add(node.className)) {
                    continue;
                }
                if (node.depth > MAX_HIERARCHY_DEPTH) {
                    return false;
                }

                List<ClassDef> defs = index.find(group, node.className);
                if (defs.size() != 1) {
                    continue;
                }

                for (String parent : defs.get(0).interfaces) {
                    if (possibleParent.equals(parent)) {
                        return true;
                    }
                    if (parent != null && parent.length() > 0) {
                        queue.addLast(new InterfaceNode(parent, node.depth + 1));
                    }
                }
            }
            return false;
        }

        private static final class InterfaceMethodCandidate {
            final ClassDef owner;
            final MethodDef method;

            InterfaceMethodCandidate(ClassDef owner, MethodDef method) {
                this.owner = owner;
                this.method = method;
            }
        }

        private String mergeMissingStatus(String current, String missingClass) {
            if (!isJdkClass(missingClass)) {
                return EXTERNAL;
            }
            return EXTERNAL.equals(current) ? current : JDK;
        }

        private MethodResolution resolveExactOwner(String group, String owner,
                                                   String name, String descriptor) {
            List<ClassDef> defs = index.find(group, owner);
            MethodKey key = new MethodKey(name, descriptor);
            if (defs.size() > 1) {
                return ambiguousDuplicateClass(defs, key);
            }
            if (defs.size() == 1) {
                MethodDef m = defs.get(0).methods.get(key);
                return m == null
                        ? MethodResolution.notFound(NOT_FOUND_IN_GROUP)
                        : MethodResolution.resolved(defs.get(0), m);
            }
            return MethodResolution.notFound(isJdkClass(owner) ? JDK : EXTERNAL);
        }

        private MethodResolution ambiguousDuplicateClass(List<ClassDef> defs, MethodKey key) {
            List<String> candidates = new ArrayList<String>();
            for (ClassDef d : defs) {
                MethodDef m = d.methods.get(key);
                if (m == null) {
                    candidates.add(d.jarPath + "!" + d.className);
                } else {
                    candidates.add(d.jarPath + "!" + d.className + "#"
                            + readableMethod(d.className, m.access, m.name,
                            m.descriptor, m.parameterNames));
                }
            }
            Collections.sort(candidates);
            return MethodResolution.ambiguous(AMBIGUOUS, candidates);
        }

        private static final class InterfaceNode {
            final String className;
            final int depth;

            InterfaceNode(String className, int depth) {
                this.className = className;
                this.depth = depth;
            }
        }
    }

    // ---------------------------------------------------------------------
    // CSV
    // ---------------------------------------------------------------------

    private static final class CsvOutputs implements Closeable {
        private final BufferedWriter classDef;
        private final BufferedWriter methodDef;
        private final BufferedWriter classRef;
        private final BufferedWriter methodCall;
        private final Stats stats;

        CsvOutputs(Path dir, Stats stats) throws IOException {
            this.stats = stats;
            classDef = newCsvWriter(dir.resolve("class_def.csv"));
            methodDef = newCsvWriter(dir.resolve("method_def.csv"));
            classRef = newCsvWriter(dir.resolve("class_ref.csv"));
            methodCall = newCsvWriter(dir.resolve("method_call.csv"));

            row(classDef, "group", "jar_path", "class_name", "class_access",
                    "super_class", "interfaces", "source_file");
            row(methodDef, "group", "jar_path", "class_name", "method_name",
                    "descriptor", "readable_method", "method_access",
                    "source_file", "first_line", "last_line");
            row(classRef, "group", "origin_jar", "origin_class", "first_origin_method",
                    "origin_source_file", "first_origin_line", "reference_kind",
                    "target_class", "target_jar", "resolution_status", "candidates");
            row(methodCall, "group", "origin_jar", "origin_class", "origin_method",
                    "origin_source_file", "origin_line", "opcode", "bytecode_owner",
                    "called_method_name", "called_descriptor", "bytecode_called_method",
                    "definition_jar", "definition_class", "definition_method",
                    "definition_source_file", "definition_first_line", "dispatch",
                    "resolution_status", "candidates");
        }

        void writeClassDef(ClassDef d) {
            row(classDef, d.group, d.jarPath, d.className, accessString(d.access),
                    safe(d.superClassName), join(d.interfaces, ";"), safe(d.sourceFile));
            stats.classDefRows++;
        }

        void writeMethodDef(ClassDef c, MethodDef m) {
            row(methodDef, c.group, c.jarPath, c.className, m.name, m.descriptor,
                    readableMethod(c.className, m.access, m.name, m.descriptor, m.parameterNames),
                    accessString(m.access), safe(c.sourceFile),
                    number(m.firstLine), number(m.lastLine));
            stats.methodDefRows++;
        }

        void writeClassRef(String group, String originJar, String originClass,
                           String originMethod, String originSource, int line,
                           String kind, String targetClass, ClassResolution r) {
            row(classRef, group, originJar, originClass, originMethod, safe(originSource),
                    number(line), kind, targetClass, r.targetJar, r.status, r.candidates);
            stats.classRefRows++;
        }

        void writeMethodCall(String group, String originJar, String originClass,
                             String originMethod, String originSource, int line,
                             String opcode, String bytecodeOwner, String calledName,
                             String calledDescriptor, String bytecodeReadable,
                             MethodResolution r, String dispatch) {
            row(methodCall, group, originJar, originClass, originMethod, safe(originSource),
                    number(line), opcode, bytecodeOwner, calledName, calledDescriptor,
                    bytecodeReadable, r.definitionJar, r.definitionClass,
                    r.definitionMethod, r.definitionSource, number(r.definitionFirstLine),
                    dispatch, r.status, r.candidates);
            stats.methodCallRows++;
        }

        @Override
        public void close() throws IOException {
            IOException first = null;
            try { classDef.close(); } catch (IOException e) { first = e; }
            try { methodDef.close(); } catch (IOException e) { if (first == null) first = e; else first.addSuppressed(e); }
            try { classRef.close(); } catch (IOException e) { if (first == null) first = e; else first.addSuppressed(e); }
            try { methodCall.close(); } catch (IOException e) { if (first == null) first = e; else first.addSuppressed(e); }
            if (first != null) {
                throw first;
            }
        }
    }

    private static BufferedWriter newCsvWriter(Path path) throws IOException {
        // Large sequential output is common. A larger buffer substantially reduces write calls
        // while remaining tiny relative to a 2 GB heap.
        return new BufferedWriter(
                new OutputStreamWriter(Files.newOutputStream(path), StandardCharsets.UTF_8),
                256 * 1024);
    }

    private static void row(BufferedWriter w, String... values) {
        try {
            for (int i = 0; i < values.length; i++) {
                if (i > 0) {
                    w.write(',');
                }
                w.write(csv(values[i]));
            }
            w.newLine();
        } catch (IOException e) {
            throw new CsvWriteException("CSV write failed", e);
        }
    }

    private static String csv(String s) {
        s = safe(s);
        if (s.indexOf(',') < 0 && s.indexOf('"') < 0
                && s.indexOf('\n') < 0 && s.indexOf('\r') < 0) {
            return s;
        }
        return '"' + s.replace("\"", "\"\"") + '"';
    }

    private static final class CsvWriteException extends RuntimeException {
        private static final long serialVersionUID = 1L;

        CsvWriteException(String message, IOException cause) {
            super(message, cause);
        }
    }

    // ---------------------------------------------------------------------
    // Type/signature helpers
    // ---------------------------------------------------------------------

    private interface TypeConsumer {
        void accept(String className);
    }

    private static void collectDescriptor(String descriptor, TypeConsumer consumer) {
        if (descriptor == null || descriptor.length() == 0) {
            return;
        }
        try {
            if (descriptor.charAt(0) == '(') {
                Type mt = Type.getMethodType(descriptor);
                Type[] args = mt.getArgumentTypes();
                for (Type arg : args) {
                    collectType(arg, consumer);
                }
                collectType(mt.getReturnType(), consumer);
            } else {
                collectType(Type.getType(descriptor), consumer);
            }
        } catch (RuntimeException ignored) {
            // Malformed descriptor: ignore this metadata item, continue the JAR.
        }
    }

    private static void collectType(Type type, TypeConsumer consumer) {
        if (type == null) {
            return;
        }
        switch (type.getSort()) {
            case Type.OBJECT:
                consumer.accept(type.getClassName());
                break;
            case Type.ARRAY:
                collectType(type.getElementType(), consumer);
                break;
            case Type.METHOD:
                Type[] args = type.getArgumentTypes();
                for (Type arg : args) {
                    collectType(arg, consumer);
                }
                collectType(type.getReturnType(), consumer);
                break;
            default:
                break;
        }
    }

    private static void collectClassOrMethodSignature(String signature, TypeConsumer consumer) {
        if (signature == null || signature.length() == 0) {
            return;
        }
        try {
            new SignatureReader(signature).accept(new CollectingSignatureVisitor(consumer));
        } catch (RuntimeException ignored) {
            // Continue other metadata.
        }
    }

    private static void collectTypeSignature(String signature, TypeConsumer consumer) {
        if (signature == null || signature.length() == 0) {
            return;
        }
        try {
            new SignatureReader(signature).acceptType(new CollectingSignatureVisitor(consumer));
        } catch (RuntimeException ignored) {
            // Continue other metadata.
        }
    }

    private static final class CollectingSignatureVisitor extends SignatureVisitor {
        private final TypeConsumer consumer;
        private String currentClassInternal;

        CollectingSignatureVisitor(TypeConsumer consumer) {
            super(ASM_API);
            this.consumer = consumer;
        }

        @Override
        public void visitClassType(String name) {
            currentClassInternal = name;
            consumer.accept(internalToClass(name));
        }

        @Override
        public void visitInnerClassType(String name) {
            if (currentClassInternal != null) {
                currentClassInternal = currentClassInternal + "$" + name;
                consumer.accept(internalToClass(currentClassInternal));
            }
        }

        @Override
        public void visitEnd() {
            currentClassInternal = null;
        }
    }

    private static void collectConstant(Object value, TypeConsumer consumer) {
        if (value instanceof Type) {
            collectType((Type) value, consumer);
        } else if (value instanceof Handle) {
            Handle h = (Handle) value;
            consumer.accept(internalToClass(h.getOwner()));
            collectDescriptor(h.getDesc(), consumer);
        } else if (value instanceof ConstantDynamic) {
            ConstantDynamic cd = (ConstantDynamic) value;
            collectDescriptor(cd.getDescriptor(), consumer);
            Handle bsm = cd.getBootstrapMethod();
            if (bsm != null) {
                consumer.accept(internalToClass(bsm.getOwner()));
                collectDescriptor(bsm.getDesc(), consumer);
            }
            for (int i = 0; i < cd.getBootstrapMethodArgumentCount(); i++) {
                collectConstant(cd.getBootstrapMethodArgument(i), consumer);
            }
        }
    }

    // ---------------------------------------------------------------------
    // JAR/class input safety
    // ---------------------------------------------------------------------

    private static boolean isClassEntry(JarEntry entry) {
        if (entry == null || entry.isDirectory()) {
            return false;
        }
        String name = entry.getName();
        if (!name.endsWith(".class")) {
            return false;
        }
        // Java 8 does not use multi-release entries. Skipping them also avoids duplicate indexing.
        return !name.startsWith("META-INF/versions/");
    }

    private static ClassReader readClassReader(JarFile jar, JarEntry entry,
                                               JarInfo info, Stats stats) {
        long declared = entry.getSize();
        if (declared > MAX_CLASS_BYTES || declared > Integer.MAX_VALUE) {
            stats.skippedClassEntries++;
            System.err.println("WARN CLASS_TOO_LARGE " + info.relativePath + "!"
                    + entry.getName() + " size=" + declared);
            return null;
        }

        InputStream in = null;
        try {
            in = jar.getInputStream(entry);

            if (declared >= 0) {
                // JAR entries normally know their uncompressed size. Allocate exactly once;
                // this avoids ByteArrayOutputStream growth and its final full-array copy.
                byte[] bytes = new byte[(int) declared];
                int offset = 0;
                while (offset < bytes.length) {
                    int n = in.read(bytes, offset, bytes.length - offset);
                    if (n < 0) {
                        stats.skippedClassEntries++;
                        System.err.println("WARN TRUNCATED_CLASS " + info.relativePath + "!"
                                + entry.getName() + " expected=" + declared + " actual=" + offset);
                        return null;
                    }
                    if (n == 0) {
                        int one = in.read();
                        if (one < 0) {
                            stats.skippedClassEntries++;
                            System.err.println("WARN TRUNCATED_CLASS " + info.relativePath + "!"
                                    + entry.getName() + " expected=" + declared + " actual=" + offset);
                            return null;
                        }
                        bytes[offset++] = (byte) one;
                    } else {
                        offset += n;
                    }
                }

                if (in.read() != -1) {
                    stats.skippedClassEntries++;
                    System.err.println("WARN CLASS_SIZE_MISMATCH " + info.relativePath + "!"
                            + entry.getName() + " declared=" + declared + " actual>declared");
                    return null;
                }
                return new ClassReader(bytes);
            }

            // Unknown entry size is uncommon. Use a bounded dynamically-grown buffer.
            byte[] buffer = new byte[8192];
            int capacity = Math.min(8192, MAX_CLASS_BYTES);
            byte[] bytes = new byte[capacity];
            int total = 0;
            int n;
            while ((n = in.read(buffer)) >= 0) {
                if (n == 0) {
                    continue;
                }
                if (total > MAX_CLASS_BYTES - n) {
                    stats.skippedClassEntries++;
                    System.err.println("WARN CLASS_TOO_LARGE " + info.relativePath + "!"
                            + entry.getName() + " uncompressed>" + MAX_CLASS_BYTES);
                    return null;
                }
                int required = total + n;
                if (required > bytes.length) {
                    int next = bytes.length;
                    while (next < required) {
                        int doubled = next << 1;
                        if (doubled <= 0 || doubled > MAX_CLASS_BYTES) {
                            next = MAX_CLASS_BYTES;
                            break;
                        }
                        next = doubled;
                    }
                    bytes = Arrays.copyOf(bytes, next);
                }
                System.arraycopy(buffer, 0, bytes, total, n);
                total += n;
            }
            if (total != bytes.length) {
                bytes = Arrays.copyOf(bytes, total);
            }
            return new ClassReader(bytes);
        } catch (IOException e) {
            stats.skippedClassEntries++;
            warn("READ_CLASS", info, entry, e);
            return null;
        } catch (RuntimeException e) {
            stats.skippedClassEntries++;
            warn("READ_CLASS", info, entry, e);
            return null;
        } finally {
            closeQuietly(in);
        }
    }

    // ---------------------------------------------------------------------
    // Model
    // ---------------------------------------------------------------------

    private static final class GroupWork {
        final String group;
        final List<JarInfo> jars;

        GroupWork(String group, List<JarInfo> jars) {
            this.group = group;
            this.jars = jars;
        }
    }

    private static final class JarInfo implements Comparable<JarInfo> {
        final Path path;
        final String relativePath;
        final String group;

        JarInfo(Path scanRoot, Path path) {
            this.path = path.toAbsolutePath().normalize();
            this.relativePath = relative(scanRoot, this.path);
            this.group = determineGroup(scanRoot, this.path);
        }

        @Override
        public int compareTo(JarInfo other) {
            int c = group.compareTo(other.group);
            return c != 0 ? c : relativePath.compareTo(other.relativePath);
        }
    }

    private static final class ClassDef {
        String group = "";
        String jarPath = "";
        String className = "";
        String superClassName = "";
        String sourceFile = "";
        int access;
        final List<String> interfaces = new ArrayList<String>();
        final Map<MethodKey, MethodDef> methods = new HashMap<MethodKey, MethodDef>();
    }

    private static final class MethodDef {
        String name = "";
        String descriptor = "";
        int access;
        int firstLine = -1;
        int lastLine = -1;
        String[] parameterNames;
    }

    private static final class MethodKey {
        final String name;
        final String descriptor;

        MethodKey(String name, String descriptor) {
            this.name = name;
            this.descriptor = descriptor;
        }

        @Override
        public boolean equals(Object o) {
            if (!(o instanceof MethodKey)) {
                return false;
            }
            MethodKey other = (MethodKey) o;
            return name.equals(other.name) && descriptor.equals(other.descriptor);
        }

        @Override
        public int hashCode() {
            return 31 * name.hashCode() + descriptor.hashCode();
        }
    }

    private static final class ClassResolution {
        String targetJar = "";
        String status = NOT_FOUND_IN_GROUP;
        String candidates = "";

        static ClassResolution resolved(String jar) {
            ClassResolution r = new ClassResolution();
            r.targetJar = jar;
            r.status = RESOLVED;
            return r;
        }

        static ClassResolution ambiguous(List<String> candidates) {
            ClassResolution r = new ClassResolution();
            r.status = AMBIGUOUS;
            r.candidates = join(candidates, ";");
            return r;
        }

        static ClassResolution notFound(String status) {
            ClassResolution r = new ClassResolution();
            r.status = status;
            return r;
        }
    }

    private static final class MethodResolution {
        String definitionJar = "";
        String definitionClass = "";
        String definitionMethod = "";
        String definitionSource = "";
        int definitionFirstLine = -1;
        String status = NOT_FOUND_IN_GROUP;
        String candidates = "";

        static MethodResolution resolved(ClassDef c, MethodDef m) {
            MethodResolution r = new MethodResolution();
            r.definitionJar = c.jarPath;
            r.definitionClass = c.className;
            r.definitionMethod = readableMethod(c.className, m.access, m.name,
                    m.descriptor, m.parameterNames);
            r.definitionSource = safe(c.sourceFile);
            r.definitionFirstLine = m.firstLine;
            r.status = RESOLVED;
            return r;
        }

        static MethodResolution ambiguous(String status, List<String> candidates) {
            MethodResolution r = new MethodResolution();
            r.status = status;
            r.candidates = join(candidates, ";");
            return r;
        }

        static MethodResolution notFound(String status) {
            MethodResolution r = new MethodResolution();
            r.status = status;
            return r;
        }
    }

    private static final class Stats {
        long classDefRows;
        long methodDefRows;
        long classRefRows;
        long methodCallRows;
        long skippedClassEntries;
    }

    // ---------------------------------------------------------------------
    // Formatting / ASM opcode helpers
    // ---------------------------------------------------------------------

    private static Type[] safeArgumentTypes(String descriptor) {
        try {
            return Type.getArgumentTypes(descriptor);
        } catch (RuntimeException e) {
            return new Type[0];
        }
    }

    private static int[] argumentSlots(int access, Type[] args) {
        int[] slots = new int[args.length];
        int slot = (access & Opcodes.ACC_STATIC) != 0 ? 0 : 1;
        for (int i = 0; i < args.length; i++) {
            slots[i] = slot;
            slot += args[i].getSize();
        }
        return slots;
    }

    private static String readableMethod(String ownerClass, int access, String name,
                                         String descriptor, String[] parameterNames) {
        Type mt;
        try {
            mt = Type.getMethodType(descriptor);
        } catch (RuntimeException e) {
            return name + descriptor;
        }

        StringBuilder sb = new StringBuilder();
        String modifiers = accessString(access);
        if (modifiers.length() > 0) {
            sb.append(modifiers).append(' ');
        }

        if ("<init>".equals(name)) {
            sb.append(simpleName(ownerClass));
        } else if ("<clinit>".equals(name)) {
            sb.append("<clinit>");
        } else {
            sb.append(mt.getReturnType().getClassName()).append(' ').append(name);
        }

        sb.append('(');
        Type[] args = mt.getArgumentTypes();
        for (int i = 0; i < args.length; i++) {
            if (i > 0) {
                sb.append(", ");
            }
            sb.append(args[i].getClassName());
            if (parameterNames != null && i < parameterNames.length
                    && parameterNames[i] != null && parameterNames[i].length() > 0) {
                sb.append(' ').append(parameterNames[i]);
            }
        }
        sb.append(')');
        return sb.toString();
    }

    private static String accessString(int access) {
        List<String> x = new ArrayList<String>();
        if ((access & Opcodes.ACC_PUBLIC) != 0) x.add("public");
        if ((access & Opcodes.ACC_PROTECTED) != 0) x.add("protected");
        if ((access & Opcodes.ACC_PRIVATE) != 0) x.add("private");
        if ((access & Opcodes.ACC_ABSTRACT) != 0) x.add("abstract");
        if ((access & Opcodes.ACC_STATIC) != 0) x.add("static");
        if ((access & Opcodes.ACC_FINAL) != 0) x.add("final");
        if ((access & Opcodes.ACC_SYNCHRONIZED) != 0) x.add("synchronized");
        if ((access & Opcodes.ACC_NATIVE) != 0) x.add("native");
        if ((access & Opcodes.ACC_STRICT) != 0) x.add("strictfp");
        return join(x, " ");
    }

    private static String fieldOpcodeName(int opcode) {
        switch (opcode) {
            case Opcodes.GETSTATIC: return "GETSTATIC";
            case Opcodes.PUTSTATIC: return "PUTSTATIC";
            case Opcodes.GETFIELD: return "GETFIELD";
            case Opcodes.PUTFIELD: return "PUTFIELD";
            default: return "FIELD_INSN_" + opcode;
        }
    }

    private static String methodOpcodeName(int opcode) {
        switch (opcode) {
            case Opcodes.INVOKEVIRTUAL: return "INVOKEVIRTUAL";
            case Opcodes.INVOKESTATIC: return "INVOKESTATIC";
            case Opcodes.INVOKESPECIAL: return "INVOKESPECIAL";
            case Opcodes.INVOKEINTERFACE: return "INVOKEINTERFACE";
            default: return "METHOD_INSN_" + opcode;
        }
    }

    private static String dispatchKind(int opcode) {
        if (opcode == Opcodes.INVOKEVIRTUAL || opcode == Opcodes.INVOKEINTERFACE) {
            return "DYNAMIC_DISPATCH_POSSIBLE";
        }
        return "STATICALLY_RESOLVED";
    }

    private static boolean isMethodHandleTag(int tag) {
        return tag == Opcodes.H_INVOKEVIRTUAL
                || tag == Opcodes.H_INVOKESTATIC
                || tag == Opcodes.H_INVOKESPECIAL
                || tag == Opcodes.H_NEWINVOKESPECIAL
                || tag == Opcodes.H_INVOKEINTERFACE;
    }

    private static String handleTagName(int tag) {
        switch (tag) {
            case Opcodes.H_INVOKEVIRTUAL: return "HANDLE_INVOKEVIRTUAL";
            case Opcodes.H_INVOKESTATIC: return "HANDLE_INVOKESTATIC";
            case Opcodes.H_INVOKESPECIAL: return "HANDLE_INVOKESPECIAL";
            case Opcodes.H_NEWINVOKESPECIAL: return "HANDLE_NEWINVOKESPECIAL";
            case Opcodes.H_INVOKEINTERFACE: return "HANDLE_INVOKEINTERFACE";
            default: return "HANDLE_" + tag;
        }
    }

    private static boolean isJava8ObjectPublicInstanceMethod(
            String name, String descriptor) {
        if ("getClass".equals(name) && "()Ljava/lang/Class;".equals(descriptor)) return true;
        if ("hashCode".equals(name) && "()I".equals(descriptor)) return true;
        if ("equals".equals(name) && "(Ljava/lang/Object;)Z".equals(descriptor)) return true;
        if ("toString".equals(name) && "()Ljava/lang/String;".equals(descriptor)) return true;
        if ("notify".equals(name) && "()V".equals(descriptor)) return true;
        if ("notifyAll".equals(name) && "()V".equals(descriptor)) return true;
        if ("wait".equals(name)) {
            return "()V".equals(descriptor)
                    || "(J)V".equals(descriptor)
                    || "(JI)V".equals(descriptor);
        }
        return false;
    }

    private static boolean isJdkClass(String className) {
        if (className == null) {
            return false;
        }
        for (String prefix : JDK_PREFIXES) {
            if (className.startsWith(prefix)) {
                return true;
            }
        }
        return false;
    }

    private static String internalToClass(String internal) {
        return internal == null ? "" : internal.replace('/', '.');
    }

    private static String simpleName(String className) {
        if (className == null) {
            return "";
        }
        int dot = className.lastIndexOf('.');
        String s = dot >= 0 ? className.substring(dot + 1) : className;
        int dollar = s.lastIndexOf('$');
        return dollar >= 0 ? s.substring(dollar + 1) : s;
    }

    private static String normalize(String s) {
        return s == null ? "" : s.replace('\\', '/');
    }

    private static String safe(String s) {
        return s == null ? "" : s;
    }

    private static String number(int n) {
        return n < 0 ? "" : Integer.toString(n);
    }

    private static String join(List<String> values, String separator) {
        if (values == null || values.isEmpty()) {
            return "";
        }
        StringBuilder sb = new StringBuilder();
        for (String value : values) {
            if (value == null || value.length() == 0) {
                continue;
            }
            if (sb.length() > 0) {
                sb.append(separator);
            }
            sb.append(value);
        }
        return sb.toString();
    }

    private static void warn(String kind, JarInfo jar, JarEntry entry, Throwable t) {
        String where = jar == null ? "" : jar.relativePath;
        if (entry != null) {
            where += "!" + entry.getName();
        }
        System.err.println("WARN " + kind + " " + where + " : "
                + t.getClass().getName() + ": " + safe(t.getMessage()));
    }

    private static void closeQuietly(Object obj) {
        if (obj == null) {
            return;
        }
        try {
            if (obj instanceof Closeable) {
                ((Closeable) obj).close();
            } else if (obj instanceof JarFile) {
                ((JarFile) obj).close();
            }
        } catch (IOException ignored) {
            // no-op
        }
    }
}
