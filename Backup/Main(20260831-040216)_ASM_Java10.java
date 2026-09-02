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
import java.sql.Connection;
import java.sql.DriverManager;
import java.sql.PreparedStatement;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.sql.Statement;
import java.text.SimpleDateFormat;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Date;
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
import java.util.Comparator;
import java.util.concurrent.Callable;
import java.util.concurrent.CompletionService;
import java.util.concurrent.ExecutorCompletionService;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;
import java.util.concurrent.ThreadFactory;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.concurrent.atomic.AtomicLong;
import java.util.jar.JarEntry;
import java.util.jar.JarFile;

/**
 * JAR/Class dependency analyzer using ASM.
 *
 * Java source/runtime target: Java 8+
 * Dependencies:
 *   - ASM 9.x core (asm-9.x.jar)
 *   - PostgreSQL JDBC driver (postgresql-42.x.x.jar)
 *
 * Usage:
 *   javac -cp asm-9.x.jar Main.java
 *   java -Xms4096m -Xmx8192m -XX:+UseG1GC \
 *        -cp .:asm-9.x.jar:postgresql-42.x.x.jar Main [scanRoot] [outputDir]
 *
 * Windows classpath separator:
 *   java -Xms4096m -Xmx8192m -XX:+UseG1GC \
 *        -cp .;asm-9.x.jar;postgresql-42.x.x.jar Main [scanRoot] [outputDir]
 *
 * Output files:
 *   processing_flow.txt  (FIXME: one Adapter method-flow sample rebuilt from PostgreSQL)
 *   CSV files are optional in the high-speed DB run (-Dasm.csvEnabled=true).
 *
 * PostgreSQL stores every Adapter-rooted flow in JAVA_ASM_PROCESSING_FLOW.
 * PostgreSQL tables are truncated at startup and populated with JDBC batch inserts.
 * The implementation remains single-threaded; batching only reduces JDBC/network round trips.
 */
public class Main {

    private static final int ASM_API = Opcodes.ASM9;

    // JVM access-flag values not needed from ASM constants directly. Keeping these local also
    // makes the class/method-context distinction explicit (some bits are intentionally reused).
    private static final int ACC_SUPER_FLAG = 0x0020;
    private static final int ACC_BRIDGE_FLAG = 0x0040;
    private static final int ACC_VARARGS_FLAG = 0x0080;
    private static final int ACC_SYNTHETIC_FLAG = 0x1000;
    private static final int ACC_ANNOTATION_FLAG = 0x2000;
    private static final int ACC_ENUM_FLAG = 0x4000;

    /** Per-class uncompressed byte limit. Prevents an abnormal/zip-bomb entry from consuming unlimited heap. */
    private static final int MAX_CLASS_BYTES = Integer.getInteger("asm.maxClassBytes", 32 * 1024 * 1024);

    /** Bounded resolver cache: speeds up repeated calls without unbounded heap growth. */
    private static final int METHOD_RESOLVE_CACHE_SIZE =
            Integer.getInteger("asm.methodResolveCacheSize", 100000);

    private static final String RESOLVED = "RESOLVED";
    private static final String AMBIGUOUS = "AMBIGUOUS_DUPLICATE_CLASS";
    private static final String AMBIGUOUS_HIERARCHY = "AMBIGUOUS_METHOD_HIERARCHY";
    private static final String NOT_FOUND_IN_GROUP = "NOT_FOUND_IN_GROUP";
    private static final String JDK = "JDK";
    private static final String EXTERNAL = "EXTERNAL_NOT_FOUND";
    private static final String HIERARCHY_LIMIT = "HIERARCHY_DEPTH_LIMIT";
    private static final int MAX_HIERARCHY_DEPTH = 256;

    /** All jp.co.* classes are indexed in memory so hierarchy resolution remains accurate. */
    private static final String TARGET_PACKAGE_PREFIX = "jp.co.";
    private static final String TARGET_INTERNAL_PREFIX = "jp/co/";

    /** These classes are indexed only for hierarchy resolution and are never emitted as call/result data. */
    private static final String EXCLUDED_FRAMEWORK_PREFIX = "jp.co.nikkobeans.framework.";

    /** PostgreSQL output is enabled by default; override with -Dasm.dbEnabled=false for CSV-only runs/tests. */
    private static final boolean DB_ENABLED = Boolean.parseBoolean(
            System.getProperty("asm.dbEnabled", "true"));
    private static final String DB_URL = System.getProperty("asm.dbUrl",
            "jdbc:postgresql://10.205.7.19:5432/postgres?reWriteBatchedInserts=true");
    private static final String DB_USER = System.getProperty("asm.dbUser", "postgres");
    private static final String DB_PASSWORD = System.getProperty("asm.dbPassword", "postgres");

    /**
     * Fast single-thread DB mode. addBatch()/executeBatch() reduces JDBC/network round trips;
     * commit remains periodic so one transaction does not grow without bound.
     */
    private static final int DB_BATCH_SIZE = Integer.getInteger("asm.dbBatchSize", 1000);
    private static final int DB_COMMIT_ROWS = Integer.getInteger("asm.dbCommitRows", 50000);
    private static final int DB_COMMIT_LOG_EVERY =
            Integer.getInteger("asm.dbCommitLogEvery", 20);

    /** Flow recursion is bounded independently from Java stack/heap limits. */
    private static final int FLOW_MAX_DEPTH = Integer.getInteger("asm.flowMaxDepth", 256);

    /**
     * Heap-pressure guard. When either threshold is crossed, expendable caches are cleared and
     * GC is requested at safe JAR/Adapter boundaries. The class index itself is retained only
     * for the current directory group because method/hierarchy resolution requires it.
     */
    private static final int MEMORY_GC_THRESHOLD_PERCENT =
            Integer.getInteger("asm.memoryGcThresholdPercent", 92);
    private static final long MEMORY_MIN_HEADROOM_MB =
            Long.getLong("asm.memoryMinHeadroomMb", 512L);
    private static final int FLOW_LOG_EVERY =
            Integer.getInteger("asm.flowLogEvery", 100);
    private static final int MEMORY_CHECK_CLASS_INTERVAL =
            Integer.getInteger("asm.memoryCheckClassInterval", 5000);
    private static final int JAR_LOG_EVERY =
            Integer.getInteger("asm.jarLogEvery", 25);

    /** Bounded cross-Adapter cache for PostgreSQL method-flow lookups. */
    private static final int FLOW_OUTGOING_CACHE_SIZE =
            Integer.getInteger("asm.flowOutgoingCacheSize", 100000);

    /**
     * CPU/I/O parallelism is applied only across independent migration systems such as
     * nkCCIS / nikkoEZ / ifaCCIS. PostgreSQL and CSV writes remain serialized through
     * CsvOutputs so one JDBC Connection/PreparedStatement set is never touched concurrently.
     */
    private static final int ANALYSIS_PARALLELISM =
            Integer.getInteger("asm.parallelism", 3);
    private static final long PARALLEL_MIN_HEAP_MB =
            Long.getLong("asm.parallelMinHeapMb", 6144L);

    /**
     * PostgreSQL is the authoritative output for the high-speed run. CSV duplicates every emitted
     * row and can become a major disk/formatting bottleneck. With DB enabled, CSV is therefore
     * disabled by default; enable explicitly with -Dasm.csvEnabled=true when files are needed.
     */
    private static final boolean CSV_ENABLED = Boolean.parseBoolean(
            System.getProperty("asm.csvEnabled", DB_ENABLED ? "false" : "true"));

    /**
     * FIXME: temporary sample-flow target requested for validation.
     * Remove this fixed target when the JavaScript/API side selects an Adapter dynamically.
     */
    private static final String FIXME_FLOW_ADAPTER = System.getProperty(
            "asm.flowAdapter",
            "jp.co.eztrade.app.tsn_meigara.unyokaisya_kanri.adapter.TsnmeigUnyCorpDelexeAdapter");

    /** Only this Adapter method is used as the processing-flow root. */
    private static final String FLOW_ROOT_METHOD = "public boolean doApplication()";

    /** Classes whose name contains this token are presentation noise for the requested flow. */
    private static final String FLOW_EXCLUDED_CLASS_TOKEN = "UnyokaisyaIchiran";

    private static final Set<String> JDK_PREFIXES = new HashSet<String>(Arrays.asList(
            "java.", "javax.", "jdk.", "sun.", "com.sun.", "org.w3c.", "org.xml.", "org.ietf."
    ));

    public static void main(String[] args) throws Exception {
        final long programStart = System.nanoTime();
        log("PROGRAM_START analysisMode=MIGRATION_PARALLEL dbWriteMode=SERIALIZED_JDBC_BATCH");

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
        if (DB_BATCH_SIZE <= 0) {
            throw new IllegalArgumentException("asm.dbBatchSize must be > 0: " + DB_BATCH_SIZE);
        }
        if (DB_COMMIT_ROWS <= 0) {
            throw new IllegalArgumentException("asm.dbCommitRows must be > 0: " + DB_COMMIT_ROWS);
        }
        if (DB_COMMIT_LOG_EVERY <= 0) {
            throw new IllegalArgumentException(
                    "asm.dbCommitLogEvery must be > 0: " + DB_COMMIT_LOG_EVERY);
        }
        if (FLOW_MAX_DEPTH <= 0) {
            throw new IllegalArgumentException("asm.flowMaxDepth must be > 0: " + FLOW_MAX_DEPTH);
        }
        if (MEMORY_GC_THRESHOLD_PERCENT < 50 || MEMORY_GC_THRESHOLD_PERCENT > 95) {
            throw new IllegalArgumentException(
                    "asm.memoryGcThresholdPercent must be between 50 and 95: "
                            + MEMORY_GC_THRESHOLD_PERCENT);
        }
        if (MEMORY_MIN_HEADROOM_MB < 32L) {
            throw new IllegalArgumentException(
                    "asm.memoryMinHeadroomMb must be >= 32: " + MEMORY_MIN_HEADROOM_MB);
        }
        if (FLOW_LOG_EVERY <= 0) {
            throw new IllegalArgumentException("asm.flowLogEvery must be > 0: " + FLOW_LOG_EVERY);
        }
        if (MEMORY_CHECK_CLASS_INTERVAL <= 0) {
            throw new IllegalArgumentException(
                    "asm.memoryCheckClassInterval must be > 0: "
                            + MEMORY_CHECK_CLASS_INTERVAL);
        }
        if (JAR_LOG_EVERY <= 0) {
            throw new IllegalArgumentException("asm.jarLogEvery must be > 0: " + JAR_LOG_EVERY);
        }
        if (FLOW_OUTGOING_CACHE_SIZE < 0) {
            throw new IllegalArgumentException(
                    "asm.flowOutgoingCacheSize must be >= 0: " + FLOW_OUTGOING_CACHE_SIZE);
        }
        if (ANALYSIS_PARALLELISM < 1 || ANALYSIS_PARALLELISM > 3) {
            throw new IllegalArgumentException(
                    "asm.parallelism must be between 1 and 3: " + ANALYSIS_PARALLELISM);
        }
        if (PARALLEL_MIN_HEAP_MB < 1024L) {
            throw new IllegalArgumentException(
                    "asm.parallelMinHeapMb must be >= 1024: " + PARALLEL_MIN_HEAP_MB);
        }

        Files.createDirectories(outputDir);

        log("CONFIG SCAN_ROOT=" + normalize(scanRoot.toString()));
        log("CONFIG OUTPUT_DIR=" + normalize(outputDir.toString()));
        log("CONFIG MAX_CLASS_BYTES=" + MAX_CLASS_BYTES);
        log("CONFIG METHOD_RESOLVE_CACHE_SIZE=" + METHOD_RESOLVE_CACHE_SIZE);
        log("CONFIG TARGET_PACKAGE=" + TARGET_PACKAGE_PREFIX + "*");
        log("CONFIG EXCLUDED_CALL_PACKAGE=" + EXCLUDED_FRAMEWORK_PREFIX + "*");
        log("CONFIG EXCLUDED_CALL_CLASS_SUFFIX=*Exception");
        log("CONFIG DB_ENABLED=" + DB_ENABLED);
        if (DB_ENABLED) {
            log("CONFIG DB_URL=" + DB_URL);
            log("CONFIG DB_USER=" + DB_USER);
            log("CONFIG DB_WRITE_MODE=SERIALIZED_JDBC_BATCH");
            log("CONFIG DB_BATCH_SIZE=" + DB_BATCH_SIZE);
            log("CONFIG DB_COMMIT_ROWS=" + DB_COMMIT_ROWS);
            log("CONFIG DB_COMMIT_LOG_EVERY=" + DB_COMMIT_LOG_EVERY);
        }
        log("CONFIG FLOW_MAX_DEPTH=" + FLOW_MAX_DEPTH);
        log("CONFIG FLOW_LOG_EVERY=" + FLOW_LOG_EVERY);
        log("CONFIG MEMORY_GC_THRESHOLD_PERCENT=" + MEMORY_GC_THRESHOLD_PERCENT);
        log("CONFIG MEMORY_MIN_HEADROOM_MB=" + MEMORY_MIN_HEADROOM_MB);
        log("CONFIG MEMORY_CHECK_CLASS_INTERVAL=" + MEMORY_CHECK_CLASS_INTERVAL);
        log("CONFIG JAR_LOG_EVERY=" + JAR_LOG_EVERY);
        log("CONFIG FLOW_OUTGOING_CACHE_SIZE=" + FLOW_OUTGOING_CACHE_SIZE);
        log("CONFIG ANALYSIS_PARALLELISM_REQUESTED=" + ANALYSIS_PARALLELISM);
        log("CONFIG PARALLEL_MIN_HEAP_MB=" + PARALLEL_MIN_HEAP_MB);
        log("CONFIG CSV_ENABLED=" + CSV_ENABLED);
        log("CONFIG FIXME_FLOW_ADAPTER=" + FIXME_FLOW_ADAPTER);
        log("CONFIG MAX_HEAP_MB=" + mb(Runtime.getRuntime().maxMemory()));

        long phase = phaseStart("DISCOVER_JARS");
        List<JarInfo> jars = discoverJars(scanRoot, outputDir);
        Collections.sort(jars);
        phaseEnd("DISCOVER_JARS jars=" + jars.size(), phase);
        if (jars.isEmpty()) {
            throw new IllegalStateException("No .jar files found under: " + scanRoot);
        }

        phase = phaseStart("GROUP_JARS");
        List<GroupWork> groups = groupJars(jars);
        phaseEnd("GROUP_JARS groups=" + groups.size(), phase);

        phase = phaseStart("GROUP_MIGRATION_SYSTEMS");
        List<MigrationWork> migrations = groupMigrationWorks(groups);
        phaseEnd("GROUP_MIGRATION_SYSTEMS migrations=" + migrations.size(), phase);

        Stats stats = new Stats();

        try (DbOutputs db = new DbOutputs();
             CsvOutputs out = new CsvOutputs(outputDir, stats, db)) {
            if (DB_ENABLED) {
                db.truncateAll();
            }

            /*
             * Parallelism policy:
             *   - independent migration systems are CPU/I/O workers (max 3)
             *   - each worker processes its directory groups sequentially
             *   - all PostgreSQL/CSV writes are serialized inside CsvOutputs
             * This keeps one JDBC batch writer while allowing JAR reading + ASM parsing +
             * method resolution to overlap across nkCCIS / nikkoEZ / ifaCCIS style systems.
             */
            processMigrationWorks(migrations, out, stats);
            out.flushAndCommit();

            if (DB_ENABLED) {
                long analyzeStart = phaseStart("DB_ANALYZE_SOURCE_TABLES");
                db.analyzeSourceTables();
                phaseEnd("DB_ANALYZE_SOURCE_TABLES", analyzeStart);

                db.prepareProcessingFlowBulkLoad();
                long flowStart = phaseStart("BUILD_ALL_ADAPTER_PROCESSING_FLOW");
                FlowBuildStats flowStats = db.rebuildAllProcessingFlows();
                stats.flowStarts = flowStats.rootCount;
                stats.processingFlowRows = flowStats.rowCount;
                stats.flowAdaptersScanned = flowStats.adapterCount;
                stats.flowAdaptersWithoutRoot = flowStats.adaptersWithoutRoot;
                phaseEnd("BUILD_ALL_ADAPTER_PROCESSING_FLOW adapters="
                        + flowStats.adapterCount + " roots=" + flowStats.rootCount
                        + " rows=" + flowStats.rowCount, flowStart);

                db.rebuildProcessingFlowIndexes();
                long flowAnalyzeStart = phaseStart("DB_ANALYZE_PROCESSING_FLOW");
                db.analyzeProcessingFlow();
                phaseEnd("DB_ANALYZE_PROCESSING_FLOW", flowAnalyzeStart);

                // Keep one text artifact for regression verification. The all-Adapter authoritative
                // data is JAVA_ASM_PROCESSING_FLOW.
                long sampleStart = phaseStart("WRITE_SAMPLE_PROCESSING_FLOW");
                db.writeFixmeMethodFlow(
                        outputDir.resolve("processing_flow.txt"), FIXME_FLOW_ADAPTER);
                phaseEnd("WRITE_SAMPLE_PROCESSING_FLOW", sampleStart);
            } else {
                writeDbFlowDisabledFile(outputDir.resolve("processing_flow.txt"));
            }
        }

        log("RESULT CLASS_DEF_ROWS=" + stats.classDefRows);
        log("RESULT METHOD_DEF_ROWS=" + stats.methodDefRows);
        log("RESULT CLASS_REF_ROWS=" + stats.classRefRows);
        log("RESULT METHOD_CALL_ROWS=" + stats.methodCallRows);
        log("RESULT CLASS_CALL_ROWS=" + stats.classCallRows);
        log("RESULT ADAPTER_INHERIT_ROWS=" + stats.adapterInheritRows);
        log("RESULT FLOW_ADAPTERS_SCANNED=" + stats.flowAdaptersScanned);
        log("RESULT FLOW_ADAPTERS_WITHOUT_ROOT=" + stats.flowAdaptersWithoutRoot);
        log("RESULT FLOW_STARTS=" + stats.flowStarts);
        log("RESULT PROCESSING_FLOW_ROWS=" + stats.processingFlowRows);
        log("RESULT SKIPPED_CLASS_ENTRIES=" + stats.skippedClassEntries.get());
        phaseEnd("PROGRAM_TOTAL", programStart);
        log("DONE");
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

    private static List<MigrationWork> groupMigrationWorks(List<GroupWork> groups) {
        Map<String, List<GroupWork>> byMigration =
                new LinkedHashMap<String, List<GroupWork>>();
        for (GroupWork group : groups) {
            String migration = migrationName(group.group);
            List<GroupWork> list = byMigration.get(migration);
            if (list == null) {
                list = new ArrayList<GroupWork>();
                byMigration.put(migration, list);
            }
            list.add(group);
        }

        List<MigrationWork> result = new ArrayList<MigrationWork>(byMigration.size());
        for (Map.Entry<String, List<GroupWork>> e : byMigration.entrySet()) {
            result.add(new MigrationWork(e.getKey(), e.getValue()));
        }

        // Start the largest independent systems first so three workers stay busy longer.
        Collections.sort(result, new Comparator<MigrationWork>() {
            @Override
            public int compare(MigrationWork a, MigrationWork b) {
                if (a.jarCount != b.jarCount) {
                    return a.jarCount > b.jarCount ? -1 : 1;
                }
                return a.name.compareTo(b.name);
            }
        });
        return result;
    }

    private static String migrationName(String group) {
        String normalized = normalize(group);
        int slash = normalized.indexOf('/');
        if (slash > 0) {
            return normalized.substring(0, slash);
        }
        return normalized.length() == 0 ? "." : normalized;
    }

    private static int effectiveAnalysisParallelism(int migrationCount) {
        if (migrationCount <= 1 || ANALYSIS_PARALLELISM <= 1) {
            return 1;
        }
        long maxHeapMb = mb(Runtime.getRuntime().maxMemory());
        if (maxHeapMb < PARALLEL_MIN_HEAP_MB) {
            log("PARALLELISM_FALLBACK requested=" + ANALYSIS_PARALLELISM
                    + " effective=1 reason=maxHeapMb(" + maxHeapMb
                    + ")<parallelMinHeapMb(" + PARALLEL_MIN_HEAP_MB + ")");
            return 1;
        }
        return Math.min(ANALYSIS_PARALLELISM, migrationCount);
    }

    private static void processMigrationWorks(final List<MigrationWork> migrations,
                                              final CsvOutputs out,
                                              final Stats stats) throws Exception {
        final int workers = effectiveAnalysisParallelism(migrations.size());
        log("ANALYSIS_EXECUTION migrations=" + migrations.size()
                + " parallelism=" + workers);

        if (workers <= 1) {
            for (MigrationWork migration : migrations) {
                processMigrationWork(migration, out, stats);
            }
            return;
        }

        final AtomicInteger threadNo = new AtomicInteger();
        ExecutorService executor = Executors.newFixedThreadPool(workers, new ThreadFactory() {
            @Override
            public Thread newThread(Runnable r) {
                Thread t = new Thread(r,
                        "asm-migration-" + threadNo.incrementAndGet());
                t.setDaemon(false);
                return t;
            }
        });
        CompletionService<Void> completion = new ExecutorCompletionService<Void>(executor);
        List<Future<Void>> futures = new ArrayList<Future<Void>>(migrations.size());
        Throwable failure = null;

        try {
            for (final MigrationWork migration : migrations) {
                futures.add(completion.submit(new Callable<Void>() {
                    @Override
                    public Void call() {
                        processMigrationWork(migration, out, stats);
                        return null;
                    }
                }));
            }

            for (int completed = 0; completed < migrations.size(); completed++) {
                try {
                    completion.take().get();
                } catch (ExecutionException e) {
                    failure = e.getCause();
                    break;
                }
            }
        } catch (InterruptedException e) {
            Thread.currentThread().interrupt();
            failure = e;
        } finally {
            if (failure != null) {
                for (Future<Void> future : futures) {
                    future.cancel(true);
                }
                executor.shutdownNow();
            } else {
                executor.shutdown();
            }
            try {
                if (!executor.awaitTermination(5, TimeUnit.MINUTES)) {
                    executor.shutdownNow();
                    if (!executor.awaitTermination(1, TimeUnit.MINUTES) && failure == null) {
                        failure = new IllegalStateException(
                                "Migration workers did not terminate after shutdown");
                    }
                }
            } catch (InterruptedException e) {
                Thread.currentThread().interrupt();
                if (failure == null) {
                    failure = e;
                }
            }
        }

        if (failure != null) {
            if (failure instanceof RuntimeException) {
                throw (RuntimeException) failure;
            }
            if (failure instanceof Error) {
                throw (Error) failure;
            }
            throw new Exception("Migration worker failed", failure);
        }
    }

    private static void processMigrationWork(MigrationWork migration,
                                             CsvOutputs out, Stats stats) {
        long migrationStart = phaseStart("MIGRATION " + migration.name
                + " groups=" + migration.groups.size()
                + " jars=" + migration.jarCount);
        for (int i = 0; i < migration.groups.size(); i++) {
            GroupWork group = migration.groups.get(i);
            String groupLabel = "GROUP " + (i + 1) + "/" + migration.groups.size()
                    + " migration=" + migration.name
                    + " " + group.group + " jars=" + group.jars.size();
            long groupStart = phaseStart(groupLabel);
            processGroup(group, out, stats);
            phaseEnd(groupLabel, groupStart);
            memoryCheckpoint("AFTER_" + groupLabel, null, false);
        }
        phaseEnd("MIGRATION " + migration.name
                + " groups=" + migration.groups.size()
                + " jars=" + migration.jarCount, migrationStart);
    }

    private static void checkWorkerCancelled() {
        if (Thread.currentThread().isInterrupted()) {
            throw new WorkerCancelledException();
        }
    }

    private static boolean shouldLogJar(int zeroBasedIndex, int total) {
        int no = zeroBasedIndex + 1;
        return zeroBasedIndex == 0 || no == total || no % JAR_LOG_EVERY == 0;
    }

    /**
     * All large, group-specific data is local to this method. Once it returns, the entire
     * class/method index and the bounded resolver cache become garbage-collectable.
     */
    private static void processGroup(GroupWork group, CsvOutputs out, Stats stats) {
        Index index = new Index();

        long passStart = phaseStart("INDEX_PASS group=" + group.group);
        for (int i = 0; i < group.jars.size(); i++) {
            checkWorkerCancelled();
            JarInfo jar = group.jars.get(i);
            boolean logJar = shouldLogJar(i, group.jars.size());
            String label = "INDEX_JAR " + (i + 1) + "/" + group.jars.size()
                    + " group=" + group.group + " jar=" + jar.relativePath;
            long jarStart = logJar ? phaseStart(label) : 0L;
            indexJar(jar, index, out, stats, logJar);
            if (logJar) {
                phaseEnd(label, jarStart);
                memoryCheckpoint(label, null, false);
            }
        }
        phaseEnd("INDEX_PASS group=" + group.group, passStart);

        long inheritStart = phaseStart("ADAPTER_INHERIT group=" + group.group);
        List<AdapterInheritEdge> inheritEdges = buildAdapterInheritance(group.group, index);
        for (AdapterInheritEdge edge : inheritEdges) {
            out.writeAdapterInherit(edge);
        }
        phaseEnd("ADAPTER_INHERIT group=" + group.group + " rows=" + inheritEdges.size(),
                inheritStart);
        inheritEdges = null;

        MethodResolver resolver = new MethodResolver(index);

        passStart = phaseStart("ANALYZE_PASS group=" + group.group);
        for (int i = 0; i < group.jars.size(); i++) {
            checkWorkerCancelled();
            JarInfo jar = group.jars.get(i);
            boolean logJar = shouldLogJar(i, group.jars.size());
            String label = "ANALYZE_JAR " + (i + 1) + "/" + group.jars.size()
                    + " group=" + group.group + " jar=" + jar.relativePath;
            long jarStart = logJar ? phaseStart(label) : 0L;
            analyzeJar(jar, index, resolver, out, stats, logJar);
            if (logJar) {
                phaseEnd(label, jarStart);
                memoryCheckpoint(label, resolver, false);
            }
        }
        phaseEnd("ANALYZE_PASS group=" + group.group, passStart);

        int cleared = resolver.clearCache();
        if (cleared > 0) {
            log("MEMORY resolverCacheCleared=" + cleared + " group=" + group.group);
        }
    }

    // ---------------------------------------------------------------------
    // PASS 1 - definitions/index
    // ---------------------------------------------------------------------

    private static void indexJar(JarInfo jarInfo, Index index, CsvOutputs out, Stats stats, boolean logSummary) {
        JarFile jar = null;
        try {
            jar = new JarFile(jarInfo.path.toFile(), false);
            java.util.Enumeration<JarEntry> entries = jar.entries();
            int indexedClasses = 0;
            while (entries.hasMoreElements()) {
                checkWorkerCancelled();
                JarEntry entry = entries.nextElement();
                // Do not even decompress/parse non-jp.co.* classes.
                if (!isTargetClassEntry(entry)) {
                    continue;
                }

                ClassReader cr = readClassReader(jar, entry, jarInfo, stats);
                if (cr == null || !isTargetInternalClassName(cr.getClassName())) {
                    continue;
                }

                DefinitionVisitor visitor = new DefinitionVisitor(jarInfo);
                try {
                    cr.accept(visitor, ClassReader.SKIP_FRAMES);
                } catch (RuntimeException e) {
                    stats.skippedClassEntries.incrementAndGet();
                    warn("INDEX_CLASS", jarInfo, entry, e);
                    continue;
                }

                if (visitor.classDef != null) {
                    // Keep every jp.co.* definition in memory for superclass/method resolution,
                    // but never emit excluded framework or *Exception classes as result data.
                    index.add(visitor.classDef);
                    if (isOutputClassName(visitor.classDef.className)) {
                        // CSV failures are deliberately not swallowed as class-parse failures.
                        // Disk-full / permission errors must stop the run instead of producing
                        // silently incomplete analysis files.
                        out.writeClassDef(visitor.classDef);
                        for (MethodDef method : visitor.classDef.methods.values()) {
                            out.writeMethodDef(visitor.classDef, method);
                        }
                    }
                    indexedClasses++;
                    if (indexedClasses % MEMORY_CHECK_CLASS_INTERVAL == 0) {
                        memoryCheckpoint("INDEX_CLASS_CHECK jar=" + jarInfo.relativePath
                                + " classes=" + indexedClasses, null, false);
                    }
                }
            }
            if (logSummary) {
                log("INDEX_JAR_SUMMARY jar=" + jarInfo.relativePath
                        + " indexedClasses=" + indexedClasses);
            }
        } catch (WorkerCancelledException e) {
            throw e;
        } catch (IOException e) {
            warn("INDEX_JAR", jarInfo, null, e);
        } catch (OutputWriteException e) {
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
            String className = internalToClass(name);
            if (!isTargetClassName(className)) {
                classDef = null;
                return;
            }

            ClassDef d = new ClassDef();
            d.group = jarInfo.group;
            d.jarPath = jarInfo.relativePath;
            d.className = className;
            d.access = access;

            String superClass = internalToClass(superName);
            d.superClassName = isTargetClassName(superClass) ? superClass : "";
            if (interfaces != null) {
                for (String intf : interfaces) {
                    String interfaceClass = internalToClass(intf);
                    if (isTargetClassName(interfaceClass)) {
                        d.interfaces.add(interfaceClass);
                    }
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
                                   CsvOutputs out, Stats stats, boolean logSummary) {
        JarFile jar = null;
        try {
            jar = new JarFile(jarInfo.path.toFile(), false);
            java.util.Enumeration<JarEntry> entries = jar.entries();
            int analyzedClasses = 0;
            // Aggregate class-call edges per JAR. This is much faster than creating/sorting a
            // graph per class, while still bounding memory far below the old group-wide graph.
            ClassCallGraph jarCallGraph = new ClassCallGraph(jarInfo.group);
            while (entries.hasMoreElements()) {
                checkWorkerCancelled();
                JarEntry entry = entries.nextElement();
                if (!isTargetClassEntry(entry)) {
                    continue;
                }

                ClassReader cr = readClassReader(jar, entry, jarInfo, stats);
                if (cr == null || !isTargetInternalClassName(cr.getClassName())) {
                    continue;
                }
                if (!isOutputInternalClassName(cr.getClassName())) {
                    continue;
                }

                try {
                    cr.accept(new DependencyVisitor(jarInfo, index, resolver, out, jarCallGraph),
                            ClassReader.SKIP_FRAMES);
                    analyzedClasses++;
                    if (analyzedClasses % MEMORY_CHECK_CLASS_INTERVAL == 0) {
                        memoryCheckpoint("ANALYZE_CLASS_CHECK jar=" + jarInfo.relativePath
                                + " classes=" + analyzedClasses, resolver, false);
                    }
                } catch (OutputWriteException e) {
                    throw e;
                } catch (RuntimeException e) {
                    stats.skippedClassEntries.incrementAndGet();
                    warn("ANALYZE_CLASS", jarInfo, entry, e);
                }
            }
            int classCallEdges = 0;
            for (ClassCallEdge edge : jarCallGraph.sortedEdges()) {
                out.writeClassCall(edge);
                classCallEdges++;
            }
            if (logSummary) {
                log("ANALYZE_JAR_SUMMARY jar=" + jarInfo.relativePath
                        + " analyzedClasses=" + analyzedClasses
                        + " classCallEdges=" + classCallEdges);
            }
        } catch (WorkerCancelledException e) {
            throw e;
        } catch (IOException e) {
            warn("ANALYZE_JAR", jarInfo, null, e);
        } catch (OutputWriteException e) {
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
        private final ClassCallGraph callGraph;

        private String originClass = "";
        private String sourceFile = "";

        /** One set per class only; discarded after each ClassReader.accept(). */
        private final Set<String> classRefDedupe = new HashSet<String>();

        DependencyVisitor(JarInfo originJar, Index index, MethodResolver resolver,
                          CsvOutputs out, ClassCallGraph callGraph) {
            super(ASM_API);
            this.originJar = originJar;
            this.index = index;
            this.resolver = resolver;
            this.out = out;
            this.callGraph = callGraph;
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

                    if (isOutputClassName(ownerClass)) {
                        MethodResolution r = resolver.resolve(
                                originJar.group, ownerClass, calledName, calledDescriptor);
                        // Exclude calls whose resolved definition is JDK/external.
                        // Missing jp.co.* targets are kept as NOT_FOUND_IN_GROUP.
                        if (!JDK.equals(r.status) && !EXTERNAL.equals(r.status)) {
                            r = sanitizeMethodResolutionForOutput(r);
                            out.writeMethodCall(originJar.group, originJar.relativePath,
                                    originClass, readableOrigin, sourceFile, line,
                                    methodOpcodeName(opcode), ownerClass, calledName, calledDescriptor,
                                    readableMethod(ownerClass, 0, calledName, calledDescriptor, null),
                                    r, dispatchKind(opcode));
                            callGraph.addCall(originJar.relativePath, originClass, ownerClass,
                                    index.resolveClass(originJar.group, ownerClass));
                        }
                    }
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

                    if (emitMethodCall && isMethodHandleTag(handle.getTag())
                            && isOutputClassName(ownerClass)) {
                        MethodResolution r = resolver.resolve(originJar.group, ownerClass,
                                handle.getName(), handle.getDesc());
                        if (!JDK.equals(r.status) && !EXTERNAL.equals(r.status)) {
                            r = sanitizeMethodResolutionForOutput(r);
                            out.writeMethodCall(originJar.group, originJar.relativePath,
                                    originClass, originMethod, sourceFile, currentLine,
                                    handleTagName(handle.getTag()), ownerClass,
                                    handle.getName(), handle.getDesc(),
                                    readableMethod(ownerClass, 0, handle.getName(),
                                            handle.getDesc(), null),
                                    r, "DYNAMIC_HANDLE");
                            callGraph.addCall(originJar.relativePath, originClass, ownerClass,
                                    index.resolveClass(originJar.group, ownerClass));
                        }
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
            if (!isOutputClassName(originClass) || !isOutputClassName(targetClass)
                    || targetClass.equals(originClass)) {
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

        ClassDef findExact(String group, String className, String jarPath) {
            for (ClassDef d : find(group, className)) {
                if (d.jarPath.equals(jarPath)) {
                    return d;
                }
            }
            return null;
        }

        List<String> classNames(String group) {
            Map<String, List<ClassDef>> byClass = classes.get(group);
            if (byClass == null || byClass.isEmpty()) {
                return Collections.emptyList();
            }
            List<String> result = new ArrayList<String>(byClass.keySet());
            Collections.sort(result);
            return result;
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
            // Only jp.co.* reaches this resolver. A missing target therefore means
            // "not found in this directory group", not third-party/JDK.
            return ClassResolution.notFound(NOT_FOUND_IN_GROUP);
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

        int clearCache() {
            if (cache == null || cache.isEmpty()) {
                return 0;
            }
            int size = cache.size();
            cache.clear();
            return size;
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
                // owner is jp.co.* because non-target packages are filtered before resolution.
                return MethodResolution.notFound(NOT_FOUND_IN_GROUP);
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
            if (isTargetClassName(missingClass)) {
                return NOT_FOUND_IN_GROUP;
            }
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
            return MethodResolution.notFound(
                    isTargetClassName(owner) ? NOT_FOUND_IN_GROUP
                            : (isJdkClass(owner) ? JDK : EXTERNAL));
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
    // Adapter inheritance metadata
    // ---------------------------------------------------------------------

    private static List<AdapterInheritEdge> buildAdapterInheritance(String group, Index index) {
        List<AdapterInheritEdge> result = new ArrayList<AdapterInheritEdge>();
        for (String className : index.classNames(group)) {
            if (!isAdapterStartClass(className)) {
                continue;
            }
            List<ClassDef> starts = new ArrayList<ClassDef>(index.find(group, className));
            Collections.sort(starts, new java.util.Comparator<ClassDef>() {
                @Override
                public int compare(ClassDef a, ClassDef b) {
                    return a.jarPath.compareTo(b.jarPath);
                }
            });
            for (ClassDef start : starts) {
                String current = safe(start.superClassName);
                Set<String> visited = new HashSet<String>();
                visited.add(start.jarPath + '\u0001' + start.className);
                int depth = 0;
                while (isTargetClassName(current) && depth < MAX_HIERARCHY_DEPTH) {
                    ClassResolution resolution = index.resolveClass(group, current);
                    if (RESOLVED.equals(resolution.status) && resolution.targetJar.length() > 0) {
                        String key = resolution.targetJar + '\u0001' + current;
                        if (!visited.add(key)) {
                            break;
                        }
                    }

                    depth++;
                    AdapterInheritEdge edge = new AdapterInheritEdge();
                    edge.group = group;
                    edge.adapterJar = start.jarPath;
                    edge.adapterClass = start.className;
                    edge.depth = depth;
                    edge.superClass = current;
                    edge.superJar = safe(resolution.targetJar);
                    edge.resolutionStatus = safe(resolution.status);
                    edge.candidates = safe(resolution.candidates);
                    result.add(edge);

                    if (!RESOLVED.equals(resolution.status) || resolution.targetJar.length() == 0) {
                        break;
                    }
                    ClassDef resolved = index.findExact(group, current, resolution.targetJar);
                    if (resolved == null) {
                        break;
                    }
                    current = safe(resolved.superClassName);
                }
            }
        }
        Collections.sort(result);
        return result;
    }

    // ---------------------------------------------------------------------
    // Class-call graph / Adapter-rooted text flow
    // ---------------------------------------------------------------------

    private static final class ClassCallGraph {
        private final String group;
        private final Map<String, Map<String, ClassCallEdge>> edgesByOrigin =
                new HashMap<String, Map<String, ClassCallEdge>>();

        ClassCallGraph(String group) {
            this.group = group;
        }

        void addCall(String originJar, String originClass, String targetClass, ClassResolution r) {
            if (!isOutputClassName(originClass) || !isOutputClassName(targetClass)
                    || originClass.equals(targetClass)) {
                return;
            }
            String originKey = graphKey(originJar, originClass);
            Map<String, ClassCallEdge> byTarget = edgesByOrigin.get(originKey);
            if (byTarget == null) {
                byTarget = new HashMap<String, ClassCallEdge>();
                edgesByOrigin.put(originKey, byTarget);
            }
            ClassCallEdge edge = byTarget.get(targetClass);
            if (edge == null) {
                edge = new ClassCallEdge();
                edge.group = group;
                edge.originJar = safe(originJar);
                edge.originClass = originClass;
                edge.targetClass = targetClass;
                edge.targetJar = safe(r.targetJar);
                edge.resolutionStatus = safe(r.status);
                edge.candidates = safe(r.candidates);
                byTarget.put(targetClass, edge);
            }
            edge.callCount++;
        }

        List<ClassCallEdge> outgoing(String originJar, String originClass) {
            Map<String, ClassCallEdge> byTarget = edgesByOrigin.get(graphKey(originJar, originClass));
            if (byTarget == null || byTarget.isEmpty()) {
                return Collections.emptyList();
            }
            List<ClassCallEdge> result = new ArrayList<ClassCallEdge>(byTarget.values());
            Collections.sort(result);
            return result;
        }

        private String graphKey(String jar, String className) {
            return safe(jar) + '\u0001' + safe(className);
        }

        List<ClassCallEdge> sortedEdges() {
            List<ClassCallEdge> result = new ArrayList<ClassCallEdge>();
            for (Map<String, ClassCallEdge> byTarget : edgesByOrigin.values()) {
                result.addAll(byTarget.values());
            }
            Collections.sort(result);
            return result;
        }
    }

    private static final class ClassCallEdge implements Comparable<ClassCallEdge> {
        String group = "";
        String originJar = "";
        String originClass = "";
        String targetClass = "";
        String targetJar = "";
        String resolutionStatus = "";
        String candidates = "";
        long callCount;

        @Override
        public int compareTo(ClassCallEdge other) {
            int c = originJar.compareTo(other.originJar);
            if (c != 0) {
                return c;
            }
            c = originClass.compareTo(other.originClass);
            if (c != 0) {
                return c;
            }
            return targetClass.compareTo(other.targetClass);
        }
    }

    /**
     * Temporary method-level flow renderer used only for the requested validation sample.
     *
     * The authoritative source is PostgreSQL JAVA_ASM_METHOD_CALL. This intentionally avoids
     * retaining a method-call graph for an entire directory group in heap. Each method expansion
     * fetches only that method's outgoing calls and closes its ResultSet before recursing.
     */
    private static final class DbMethodFlowTextOutput implements Closeable {
        private final BufferedWriter writer;
        private final PreparedStatement adapterLocations;
        private final PreparedStatement originMethods;
        private final PreparedStatement outgoingCalls;

        DbMethodFlowTextOutput(Connection connection, Path path) throws SQLException, IOException {
            PreparedStatement a = null;
            PreparedStatement o = null;
            PreparedStatement calls = null;
            BufferedWriter w = null;
            try {
                a = connection.prepareStatement(
                        "SELECT GROUP_NAME,JAR_PATH FROM JAVA_ASM_CLASS_DEF "
                                + "WHERE CLASS_NAME=? AND IS_ADAPTER=TRUE "
                                + "ORDER BY GROUP_NAME,JAR_PATH");
                o = connection.prepareStatement(
                        "SELECT ORIGIN_METHOD,MIN(ID) AS FIRST_ID FROM JAVA_ASM_METHOD_CALL "
                                + "WHERE GROUP_NAME=? AND ORIGIN_JAR=? AND ORIGIN_CLASS=? "
                                + "GROUP BY ORIGIN_METHOD ORDER BY FIRST_ID,ORIGIN_METHOD");
                calls = connection.prepareStatement(
                        "SELECT ID,ORIGIN_LINE,OPCODE,BYTECODE_OWNER,CALLED_METHOD_NAME,"
                                + "CALLED_DESCRIPTOR,BYTECODE_CALLED_METHOD,DEFINITION_JAR,"
                                + "DEFINITION_CLASS,DEFINITION_METHOD,DISPATCH,RESOLUTION_STATUS,"
                                + "CANDIDATES FROM JAVA_ASM_METHOD_CALL "
                                + "WHERE GROUP_NAME=? AND ORIGIN_JAR=? AND ORIGIN_CLASS=? "
                                + "AND ORIGIN_METHOD=? ORDER BY ID");
                try {
                    calls.setFetchSize(256);
                } catch (SQLException ignored) {
                    // Some JDBC drivers may reject fetch-size hints. Correctness is unaffected.
                }
                w = new BufferedWriter(
                        new OutputStreamWriter(Files.newOutputStream(path), StandardCharsets.UTF_8),
                        256 * 1024);
            } catch (SQLException e) {
                closeQuietly(a);
                closeQuietly(o);
                closeQuietly(calls);
                closeQuietly(w);
                throw e;
            } catch (IOException e) {
                closeQuietly(a);
                closeQuietly(o);
                closeQuietly(calls);
                closeQuietly(w);
                throw e;
            }
            adapterLocations = a;
            originMethods = o;
            outgoingCalls = calls;
            writer = w;
        }

        long writeAdapter(String adapterClass) {
            writeLine("# FIXME temporary PostgreSQL method-call flow sample");
            writeLine("# Source: JAVA_ASM_METHOD_CALL / JAVA_ASM_CLASS_DEF");
            writeLine("# Start Adapter: " + adapterClass);
            writeLine("# Root method: " + FLOW_ROOT_METHOD + " only.");
            writeLine("# Hidden from flow: caller/callee in any .framework. or .util. package;"
                    + " *Bean/*Exception classes; classes containing " + FLOW_EXCLUDED_CLASS_TOKEN
                    + "; constructors; close(); and method names containing Bean.");
            writeLine("# Calls are emitted in JAVA_ASM_METHOD_CALL.ID order, which follows ASM"
                    + " bytecode visitation/insertion order.");
            writeLine("# This is a static bytecode call-flow approximation; branches, loops and"
                    + " runtime polymorphic dispatch are not an execution trace.");
            writeLine("");

            long starts = 0;
            ResultSet rs = null;
            try {
                adapterLocations.clearParameters();
                adapterLocations.setString(1, adapterClass);
                rs = adapterLocations.executeQuery();
                while (rs.next()) {
                    String group = safe(rs.getString(1));
                    String jar = safe(rs.getString(2));
                    starts++;
                    writeLocation(group, jar, adapterClass);
                }
            } catch (SQLException e) {
                throw new OutputWriteException("PostgreSQL flow start lookup failed", e);
            } finally {
                closeQuietly(rs);
            }

            if (starts == 0) {
                writeLine("[NO_ADAPTER_FOUND] No matching Adapter exists in JAVA_ASM_CLASS_DEF.");
            }
            return starts;
        }

        private void writeLocation(String group, String jar, String adapterClass) {
            List<String> methods = loadOriginMethods(group, jar, adapterClass);
            List<String> roots = new ArrayList<String>(1);
            for (String method : methods) {
                if (FLOW_ROOT_METHOD.equals(method)) {
                    roots.add(method);
                    break;
                }
            }

            writeLine("============================================================");
            writeLine("GROUP: " + group);
            writeLine("START: " + adapterClass + " [jar=" + jar + "]");
            writeLine("ROOT_METHOD_COUNT: " + roots.size());

            if (roots.isEmpty()) {
                writeLine("  [NO_ROOT_METHOD] " + FLOW_ROOT_METHOD
                        + " was not found in JAVA_ASM_METHOD_CALL for this Adapter.");
                writeLine("");
                return;
            }

            int rootNo = 0;
            for (String rootMethod : roots) {
                rootNo++;
                writeLine("");
                writeLine("ROOT " + rootNo + ": " + simpleName(adapterClass)
                        + " :: " + rootMethod);

                FlowMethodKey root = new FlowMethodKey(group, jar, adapterClass, rootMethod);
                Set<FlowMethodKey> path = new HashSet<FlowMethodKey>();
                Set<FlowMethodKey> expanded = new HashSet<FlowMethodKey>();
                path.add(root);
                writeChildren(root, 1, path, expanded);
            }
            writeLine("");
        }

        private List<String> loadOriginMethods(String group, String jar, String className) {
            List<String> result = new ArrayList<String>();
            ResultSet rs = null;
            try {
                originMethods.clearParameters();
                originMethods.setString(1, group);
                originMethods.setString(2, jar);
                originMethods.setString(3, className);
                rs = originMethods.executeQuery();
                while (rs.next()) {
                    String method = safe(rs.getString(1));
                    if (method.length() > 0) {
                        result.add(method);
                    }
                }
                return result;
            } catch (SQLException e) {
                throw new OutputWriteException("PostgreSQL flow root-method lookup failed", e);
            } finally {
                closeQuietly(rs);
            }
        }

        private void writeChildren(FlowMethodKey origin, int depth,
                                   Set<FlowMethodKey> path, Set<FlowMethodKey> expanded) {
            if (depth > FLOW_MAX_DEPTH) {
                writeLine(indent(depth) + "-> [DEPTH_LIMIT " + FLOW_MAX_DEPTH + "]");
                return;
            }
            if (!expanded.add(origin)) {
                return;
            }

            List<FlowCall> calls = loadOutgoing(origin);
            int visibleSequence = 0;
            for (FlowCall call : calls) {
                String targetClass = call.targetClass();
                String targetMethod = call.targetMethod();

                // Flow presentation filtering is intentionally separate from the raw ASM tables.
                // Apply every display rule to both sides of the edge before numbering/output.
                if (!isFlowVisibleCall(origin, call, targetClass)) {
                    continue;
                }

                visibleSequence++;
                StringBuilder line = new StringBuilder();
                line.append(indent(depth)).append(visibleSequence).append(". -> ")
                        .append(simpleName(targetClass)).append(" :: ").append(targetMethod);
                if (call.originLine >= 0) {
                    line.append(" [line=").append(call.originLine).append(']');
                }
                if (call.opcode.length() > 0) {
                    line.append(" [").append(call.opcode).append(']');
                }
                if (call.dispatch.length() > 0) {
                    line.append(" [dispatch=").append(call.dispatch).append(']');
                }
                if (!RESOLVED.equals(call.status)) {
                    line.append(" [status=").append(call.status).append(']');
                }

                if (!call.isResolvedTarget()) {
                    writeLine(line.toString());
                    continue;
                }

                FlowMethodKey target = new FlowMethodKey(origin.group, call.definitionJar,
                        call.definitionClass, call.definitionMethod);
                if (path.contains(target)) {
                    line.append(" [CYCLE]");
                    writeLine(line.toString());
                    continue;
                }
                if (expanded.contains(target)) {
                    line.append(" [ALREADY_EXPANDED]");
                    writeLine(line.toString());
                    continue;
                }

                writeLine(line.toString());
                path.add(target);
                writeChildren(target, depth + 1, path, expanded);
                path.remove(target);
            }
        }

        private List<FlowCall> loadOutgoing(FlowMethodKey origin) {
            List<FlowCall> result = new ArrayList<FlowCall>();
            ResultSet rs = null;
            try {
                outgoingCalls.clearParameters();
                outgoingCalls.setString(1, origin.group);
                outgoingCalls.setString(2, origin.jar);
                outgoingCalls.setString(3, origin.className);
                outgoingCalls.setString(4, origin.method);
                rs = outgoingCalls.executeQuery();
                while (rs.next()) {
                    FlowCall call = new FlowCall();
                    call.id = rs.getLong(1);
                    int line = rs.getInt(2);
                    call.originLine = rs.wasNull() ? -1 : line;
                    call.opcode = safe(rs.getString(3));
                    call.bytecodeOwner = safe(rs.getString(4));
                    call.calledMethodName = safe(rs.getString(5));
                    call.calledDescriptor = safe(rs.getString(6));
                    call.bytecodeCalledMethod = safe(rs.getString(7));
                    call.definitionJar = safe(rs.getString(8));
                    call.definitionClass = safe(rs.getString(9));
                    call.definitionMethod = safe(rs.getString(10));
                    call.dispatch = safe(rs.getString(11));
                    call.status = safe(rs.getString(12));
                    call.candidates = safe(rs.getString(13));
                    result.add(call);
                }
                return result;
            } catch (SQLException e) {
                throw new OutputWriteException("PostgreSQL flow outgoing-call lookup failed: "
                        + origin, e);
            } finally {
                closeQuietly(rs);
            }
        }

        private void writeLine(String text) {
            try {
                writer.write(text);
                writer.newLine();
            } catch (IOException e) {
                throw new OutputWriteException("Flow text write failed", e);
            }
        }

        @Override
        public void close() throws IOException {
            closeQuietly(adapterLocations);
            closeQuietly(originMethods);
            closeQuietly(outgoingCalls);
            writer.close();
        }
    }


    /**
     * Builds every Adapter-rooted processing flow directly into JAVA_ASM_PROCESSING_FLOW.
     *
     * Memory policy:
     * - Only the small Adapter-root metadata list is retained across roots.
     * - One method's outgoing calls are loaded at a time and reused through a bounded LRU cache.
     * - path/expanded sets are discarded after every Adapter.
     * - DB writes use JDBC batch on the same single thread.
     */
    private static final class DbProcessingFlowOutput implements Closeable {
        private final Connection connection;
        private final PreparedStatement adapterRoots;
        private final PreparedStatement outgoingCalls;
        private final PreparedStatement insertFlow;
        private final Map<FlowMethodKey, List<FlowCall>> outgoingCache;
        private int insertBatchCount;
        private int rowsSinceCommit;
        private long commitCount;

        DbProcessingFlowOutput(Connection connection) throws SQLException {
            this.connection = connection;
            PreparedStatement roots = null;
            PreparedStatement calls = null;
            PreparedStatement insert = null;
            try {
                roots = connection.prepareStatement(
                        "SELECT DISTINCT c.GROUP_NAME,c.JAR_PATH,c.CLASS_NAME,m.READABLE_METHOD "
                                + "FROM JAVA_ASM_CLASS_DEF c "
                                + "LEFT JOIN JAVA_ASM_METHOD_DEF m ON "
                                + "m.GROUP_NAME=c.GROUP_NAME AND m.JAR_PATH=c.JAR_PATH "
                                + "AND m.CLASS_NAME=c.CLASS_NAME "
                                + "AND m.METHOD_NAME='doApplication' AND m.DESCRIPTOR='()Z' "
                                + "AND m.METHOD_ACCESS='public' "
                                + "WHERE c.IS_ADAPTER=TRUE "
                                + "ORDER BY c.GROUP_NAME,c.JAR_PATH,c.CLASS_NAME");
                try {
                    roots.setFetchSize(256);
                } catch (SQLException ignored) {
                    // Performance hint only.
                }

                calls = connection.prepareStatement(
                        "SELECT ID,ORIGIN_LINE,OPCODE,BYTECODE_OWNER,CALLED_METHOD_NAME,"
                                + "CALLED_DESCRIPTOR,BYTECODE_CALLED_METHOD,DEFINITION_JAR,"
                                + "DEFINITION_CLASS,DEFINITION_METHOD,DISPATCH,RESOLUTION_STATUS,"
                                + "CANDIDATES FROM JAVA_ASM_METHOD_CALL "
                                + "WHERE GROUP_NAME=? AND ORIGIN_JAR=? AND ORIGIN_CLASS=? "
                                + "AND ORIGIN_METHOD=? ORDER BY ID");
                try {
                    calls.setFetchSize(128);
                } catch (SQLException ignored) {
                    // Performance hint only.
                }

                insert = connection.prepareStatement(
                        "INSERT INTO JAVA_ASM_PROCESSING_FLOW "
                                + "(GROUP_NAME,ADAPTER_JAR,ADAPTER_CLASS,ROOT_METHOD,FLOW_ORDER,"
                                + "DEPTH,FLOW_PATH,SIBLING_NO,NODE_JAR,NODE_CLASS,NODE_METHOD,"
                                + "PARENT_JAR,PARENT_CLASS,PARENT_METHOD,ORIGIN_LINE,OPCODE,DISPATCH,"
                                + "RESOLUTION_STATUS,RAW_METHOD_CALL_ID,IS_CYCLE,IS_ALREADY_EXPANDED,"
                                + "CANDIDATES) VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)");
            } catch (SQLException e) {
                closeQuietly(roots);
                closeQuietly(calls);
                closeQuietly(insert);
                throw e;
            }
            adapterRoots = roots;
            outgoingCalls = calls;
            insertFlow = insert;
            if (FLOW_OUTGOING_CACHE_SIZE == 0) {
                outgoingCache = null;
            } else {
                outgoingCache = new LinkedHashMap<FlowMethodKey, List<FlowCall>>(4096, 0.75f, true) {
                    private static final long serialVersionUID = 1L;
                    @Override
                    protected boolean removeEldestEntry(
                            Map.Entry<FlowMethodKey, List<FlowCall>> eldest) {
                        return size() > FLOW_OUTGOING_CACHE_SIZE;
                    }
                };
            }
        }

        FlowBuildStats writeAllAdapters() {
            List<FlowRoot> roots = loadRoots();
            FlowBuildStats stats = new FlowBuildStats();
            stats.adapterCount = roots.size();

            for (int rootIndex = 0; rootIndex < roots.size(); rootIndex++) {
                FlowRoot root = roots.get(rootIndex);
                boolean logThis = ((rootIndex + 1) % FLOW_LOG_EVERY == 0)
                        || rootIndex == 0 || rootIndex + 1 == roots.size();
                long adapterStart = System.nanoTime();
                if (logThis) {
                    log("FLOW_ADAPTER_START " + (rootIndex + 1) + "/" + roots.size()
                            + " class=" + root.className + " jar=" + root.jar);
                }

                if (root.rootMethod.length() == 0) {
                    stats.adaptersWithoutRoot++;
                    if (logThis) {
                        log("FLOW_ADAPTER_END " + (rootIndex + 1) + "/" + roots.size()
                                + " class=" + root.className + " status=NO_ROOT"
                                + " elapsed=" + formatElapsed(adapterStart));
                    }
                    continue;
                }

                stats.rootCount++;
                FlowBuildContext context = new FlowBuildContext(root);

                insertNode(context, 0L, 0, "ROOT", 0,
                        root.jar, root.className, root.rootMethod,
                        "", "", "", -1, "", "", 0L,
                        false, false, "", "ROOT");
                stats.rowCount++;

                FlowMethodKey rootKey = new FlowMethodKey(
                        root.group, root.jar, root.className, root.rootMethod);
                Set<FlowMethodKey> path = new HashSet<FlowMethodKey>();
                Set<FlowMethodKey> expanded = new HashSet<FlowMethodKey>();
                path.add(rootKey);
                long childRows = writeChildren(context, rootKey, 1, "", path, expanded);
                stats.rowCount += childRows;

                if (logThis) {
                    log("FLOW_ADAPTER_END " + (rootIndex + 1) + "/" + roots.size()
                            + " class=" + root.className
                            + " rows=" + (childRows + 1L)
                            + " expandedMethods=" + expanded.size()
                            + " elapsed=" + formatElapsed(adapterStart)
                            + " " + memorySummary());
                }

                // Heap-pressure checks are only needed on progress-log boundaries.
                if (logThis) {
                    memoryCheckpoint("FLOW_ADAPTER " + (rootIndex + 1) + "/" + roots.size(),
                            null, false);
                }
            }

            commitPending("PROCESSING_FLOW_FINAL");
            roots.clear();
            return stats;
        }

        private List<FlowRoot> loadRoots() {
            List<FlowRoot> result = new ArrayList<FlowRoot>();
            ResultSet rs = null;
            try {
                rs = adapterRoots.executeQuery();
                while (rs.next()) {
                    FlowRoot root = new FlowRoot();
                    root.group = safe(rs.getString(1));
                    root.jar = safe(rs.getString(2));
                    root.className = safe(rs.getString(3));
                    root.rootMethod = safe(rs.getString(4));
                    result.add(root);
                }
                log("FLOW_ROOT_LOOKUP adapters=" + result.size() + " " + memorySummary());
                return result;
            } catch (SQLException e) {
                throw new OutputWriteException("PostgreSQL all-Adapter flow root lookup failed", e);
            } finally {
                closeQuietly(rs);
            }
        }

        private long writeChildren(FlowBuildContext context, FlowMethodKey origin, int depth,
                                   String parentPath, Set<FlowMethodKey> path,
                                   Set<FlowMethodKey> expanded) {
            if (depth > FLOW_MAX_DEPTH) {
                logError("WARN FLOW_DEPTH_LIMIT adapter=" + context.root.className
                        + " origin=" + origin + " maxDepth=" + FLOW_MAX_DEPTH);
                return 0L;
            }
            if (!expanded.add(origin)) {
                return 0L;
            }

            List<FlowCall> calls = loadOutgoing(origin);
            int visibleSequence = 0;
            long written = 0L;
            for (FlowCall call : calls) {
                    String targetClass = call.targetClass();
                    if (!isFlowVisibleCall(origin, call, targetClass)) {
                        continue;
                    }

                    visibleSequence++;
                    String flowPath = parentPath.length() == 0
                            ? Integer.toString(visibleSequence)
                            : parentPath + "." + visibleSequence;
                    String targetMethod = call.targetMethod();
                    boolean cycle = false;
                    boolean alreadyExpanded = false;
                    FlowMethodKey target = null;

                    if (call.isResolvedTarget()) {
                        target = new FlowMethodKey(origin.group, call.definitionJar,
                                call.definitionClass, call.definitionMethod);
                        cycle = path.contains(target);
                        alreadyExpanded = !cycle && expanded.contains(target);
                    }

                    long order = ++context.lastOrder;
                    insertNode(context, order, depth, flowPath, visibleSequence,
                            call.isResolvedTarget() ? call.definitionJar : "",
                            targetClass, targetMethod,
                            origin.jar, origin.className, origin.method,
                            call.originLine, call.opcode, call.dispatch, call.id,
                            cycle, alreadyExpanded, call.candidates, call.status);
                    written++;

                    if (!call.isResolvedTarget() || cycle || alreadyExpanded) {
                        continue;
                    }

                    path.add(target);
                    written += writeChildren(context, target, depth + 1, flowPath, path, expanded);
                    path.remove(target);
            }
            return written;
        }

        private List<FlowCall> loadOutgoing(FlowMethodKey origin) {
            if (outgoingCache != null) {
                List<FlowCall> cached = outgoingCache.get(origin);
                if (cached != null) {
                    return cached;
                }
            }
            List<FlowCall> result = new ArrayList<FlowCall>();
            ResultSet rs = null;
            try {
                outgoingCalls.clearParameters();
                outgoingCalls.setString(1, origin.group);
                outgoingCalls.setString(2, origin.jar);
                outgoingCalls.setString(3, origin.className);
                outgoingCalls.setString(4, origin.method);
                rs = outgoingCalls.executeQuery();
                while (rs.next()) {
                    FlowCall call = new FlowCall();
                    call.id = rs.getLong(1);
                    int line = rs.getInt(2);
                    call.originLine = rs.wasNull() ? -1 : line;
                    call.opcode = safe(rs.getString(3));
                    call.bytecodeOwner = safe(rs.getString(4));
                    call.calledMethodName = safe(rs.getString(5));
                    call.calledDescriptor = safe(rs.getString(6));
                    call.bytecodeCalledMethod = safe(rs.getString(7));
                    call.definitionJar = safe(rs.getString(8));
                    call.definitionClass = safe(rs.getString(9));
                    call.definitionMethod = safe(rs.getString(10));
                    call.dispatch = safe(rs.getString(11));
                    call.status = safe(rs.getString(12));
                    call.candidates = safe(rs.getString(13));
                    result.add(call);
                }
                if (outgoingCache != null) {
                    outgoingCache.put(origin, result);
                }
                return result;
            } catch (SQLException e) {
                throw new OutputWriteException(
                        "PostgreSQL all-Adapter flow outgoing-call lookup failed: " + origin, e);
            } finally {
                closeQuietly(rs);
            }
        }

        private void insertNode(FlowBuildContext context, long order, int depth,
                                String flowPath, int siblingNo,
                                String nodeJar, String nodeClass, String nodeMethod,
                                String parentJar, String parentClass, String parentMethod,
                                int originLine, String opcode, String dispatch, long rawCallId,
                                boolean cycle, boolean alreadyExpanded, String candidates,
                                String resolutionStatus) {
            try {
                int i = 1;
                insertFlow.setString(i++, context.root.group);
                insertFlow.setString(i++, context.root.jar);
                insertFlow.setString(i++, context.root.className);
                insertFlow.setString(i++, context.root.rootMethod);
                insertFlow.setLong(i++, order);
                insertFlow.setInt(i++, depth);
                insertFlow.setString(i++, flowPath);
                insertFlow.setInt(i++, siblingNo);
                insertFlow.setString(i++, safe(nodeJar));
                insertFlow.setString(i++, safe(nodeClass));
                insertFlow.setString(i++, safe(nodeMethod));
                insertFlow.setString(i++, safe(parentJar));
                insertFlow.setString(i++, safe(parentClass));
                insertFlow.setString(i++, safe(parentMethod));
                if (originLine < 0) {
                    insertFlow.setNull(i++, java.sql.Types.INTEGER);
                } else {
                    insertFlow.setInt(i++, originLine);
                }
                insertFlow.setString(i++, safe(opcode));
                insertFlow.setString(i++, safe(dispatch));
                insertFlow.setString(i++, safe(resolutionStatus));
                if (rawCallId <= 0L) {
                    insertFlow.setNull(i++, java.sql.Types.BIGINT);
                } else {
                    insertFlow.setLong(i++, rawCallId);
                }
                insertFlow.setBoolean(i++, cycle);
                insertFlow.setBoolean(i++, alreadyExpanded);
                insertFlow.setString(i++, safe(candidates));

                insertFlow.addBatch();
                insertBatchCount++;
                rowsSinceCommit++;
                if (insertBatchCount >= DB_BATCH_SIZE) {
                    flushInsertBatch();
                }
                if (rowsSinceCommit >= DB_COMMIT_ROWS) {
                    commitPending("PROCESSING_FLOW");
                }
            } catch (SQLException e) {
                rollbackQuietly();
                logError("ERROR JAVA_ASM_PROCESSING_FLOW insert failed adapter="
                        + context.root.className + " flowPath=" + flowPath
                        + " node=" + nodeClass + " method=" + nodeMethod
                        + " sqlState=" + safe(e.getSQLState())
                        + " errorCode=" + e.getErrorCode()
                        + " message=" + safe(e.getMessage()));
                throw new OutputWriteException("JAVA_ASM_PROCESSING_FLOW insert failed adapter="
                        + context.root.className + " flowPath=" + flowPath
                        + " node=" + nodeClass + " method=" + nodeMethod, e);
            }
        }

        private void flushInsertBatch() throws SQLException {
            if (insertBatchCount <= 0) {
                return;
            }
            int[] results = insertFlow.executeBatch();
            for (int result : results) {
                if (result == Statement.EXECUTE_FAILED) {
                    throw new SQLException("JAVA_ASM_PROCESSING_FLOW JDBC batch reported EXECUTE_FAILED");
                }
            }
            insertBatchCount = 0;
        }

        private void commitPending(String source) {
            if (rowsSinceCommit <= 0) {
                return;
            }
            try {
                int committedRows = rowsSinceCommit;
                flushInsertBatch();
                connection.commit();
                rowsSinceCommit = 0;
                commitCount++;
                if (commitCount % DB_COMMIT_LOG_EVERY == 0) {
                    log("DB_COMMIT source=" + source + " commitNo=" + commitCount
                            + " rows=" + committedRows + " " + memorySummary());
                }
            } catch (SQLException e) {
                rollbackQuietly();
                throw new OutputWriteException(
                        "JAVA_ASM_PROCESSING_FLOW batch commit failed", e);
            }
        }

        private void rollbackQuietly() {
            rowsSinceCommit = 0;
            insertBatchCount = 0;
            try { insertFlow.clearBatch(); } catch (SQLException ignored) { }
            try {
                connection.rollback();
            } catch (SQLException ignored) {
                // no-op
            }
        }

        @Override
        public void close() throws IOException {
            // Do not auto-commit here after a failure. writeAllAdapters() commits on its successful
            // path, while an exception rolls back the current transaction.
            if (outgoingCache != null) {
                outgoingCache.clear();
            }
            closeQuietly(insertFlow);
            closeQuietly(outgoingCalls);
            closeQuietly(adapterRoots);
        }
    }

    private static final class FlowRoot {
        String group = "";
        String jar = "";
        String className = "";
        String rootMethod = "";
    }

    private static final class FlowBuildContext {
        final FlowRoot root;
        long lastOrder;

        FlowBuildContext(FlowRoot root) {
            this.root = root;
        }
    }

    private static final class FlowBuildStats {
        long adapterCount;
        long adaptersWithoutRoot;
        long rootCount;
        long rowCount;
    }

    private static final class FlowMethodKey {
        final String group;
        final String jar;
        final String className;
        final String method;

        FlowMethodKey(String group, String jar, String className, String method) {
            this.group = safe(group);
            this.jar = safe(jar);
            this.className = safe(className);
            this.method = safe(method);
        }

        @Override
        public boolean equals(Object o) {
            if (!(o instanceof FlowMethodKey)) {
                return false;
            }
            FlowMethodKey other = (FlowMethodKey) o;
            return group.equals(other.group) && jar.equals(other.jar)
                    && className.equals(other.className) && method.equals(other.method);
        }

        @Override
        public int hashCode() {
            int h = group.hashCode();
            h = 31 * h + jar.hashCode();
            h = 31 * h + className.hashCode();
            h = 31 * h + method.hashCode();
            return h;
        }

        @Override
        public String toString() {
            return group + "|" + jar + "|" + className + "|" + method;
        }
    }

    private static final class FlowCall {
        long id;
        int originLine = -1;
        String opcode = "";
        String bytecodeOwner = "";
        String calledMethodName = "";
        String calledDescriptor = "";
        String bytecodeCalledMethod = "";
        String definitionJar = "";
        String definitionClass = "";
        String definitionMethod = "";
        String dispatch = "";
        String status = "";
        String candidates = "";

        String targetClass() {
            return isResolvedTarget() ? definitionClass : bytecodeOwner;
        }

        String targetMethod() {
            if (isResolvedTarget()) {
                return definitionMethod;
            }
            if (bytecodeCalledMethod.length() > 0) {
                return bytecodeCalledMethod;
            }
            return calledMethodName + calledDescriptor;
        }

        boolean isResolvedTarget() {
            return RESOLVED.equals(status) && definitionJar.length() > 0
                    && definitionClass.length() > 0 && definitionMethod.length() > 0;
        }
    }

    private static void writeDbFlowDisabledFile(Path path) {
        try (BufferedWriter writer = new BufferedWriter(
                new OutputStreamWriter(Files.newOutputStream(path), StandardCharsets.UTF_8),
                64 * 1024)) {
            writer.write("# FIXME temporary PostgreSQL method-call flow sample");
            writer.newLine();
            writer.write("# SKIPPED: asm.dbEnabled=false, so PostgreSQL flow reconstruction is unavailable.");
            writer.newLine();
        } catch (IOException e) {
            throw new OutputWriteException("Flow disabled-marker write failed", e);
        }
    }


    private static boolean isAdapterStartClass(String className) {
        if (!isOutputClassName(className)) {
            return false;
        }
        int dot = className.lastIndexOf('.');
        String simpleName = dot >= 0 ? className.substring(dot + 1) : className;
        return simpleName.indexOf('$') < 0 && simpleName.endsWith("Adapter");
    }

    private static String indent(int depth) {
        StringBuilder b = new StringBuilder(depth * 2);
        for (int i = 0; i < depth; i++) {
            b.append("  ");
        }
        return b.toString();
    }

    // ---------------------------------------------------------------------
    // PostgreSQL
    // ---------------------------------------------------------------------

    private static final class DbOutputs implements Closeable {
        private Connection connection;
        private PreparedStatement classDef;
        private PreparedStatement methodDef;
        private PreparedStatement classRef;
        private PreparedStatement methodCall;
        private PreparedStatement classCall;
        private PreparedStatement adapterInherit;

        private int classDefBatch;
        private int methodDefBatch;
        private int classRefBatch;
        private int methodCallBatch;
        private int classCallBatch;
        private int adapterInheritBatch;
        private int rowsSinceCommit;
        private long commitCount;

        DbOutputs() throws SQLException {
            if (!DB_ENABLED) {
                return;
            }
            long start = phaseStart("DB_CONNECT");
            try {
                Class.forName("org.postgresql.Driver");
            } catch (ClassNotFoundException e) {
                throw new SQLException(
                        "PostgreSQL JDBC driver not found. Add postgresql-42.x.x.jar to classpath.", e);
            }

            connection = DriverManager.getConnection(DB_URL, DB_USER, DB_PASSWORD);
            connection.setAutoCommit(false);

            classDef = connection.prepareStatement(
                    "INSERT INTO JAVA_ASM_CLASS_DEF "
                            + "(GROUP_NAME,JAR_PATH,CLASS_NAME,CLASS_ACCESS,SUPER_CLASS,INTERFACES,"
                            + "SOURCE_FILE,IS_ADAPTER) VALUES (?,?,?,?,?,?,?,?)");
            methodDef = connection.prepareStatement(
                    "INSERT INTO JAVA_ASM_METHOD_DEF "
                            + "(GROUP_NAME,JAR_PATH,CLASS_NAME,METHOD_NAME,DESCRIPTOR,READABLE_METHOD,"
                            + "METHOD_ACCESS,SOURCE_FILE,FIRST_LINE,LAST_LINE) VALUES (?,?,?,?,?,?,?,?,?,?)");
            classRef = connection.prepareStatement(
                    "INSERT INTO JAVA_ASM_CLASS_REF "
                            + "(GROUP_NAME,ORIGIN_JAR,ORIGIN_CLASS,FIRST_ORIGIN_METHOD,ORIGIN_SOURCE_FILE,"
                            + "FIRST_ORIGIN_LINE,REFERENCE_KIND,TARGET_CLASS,TARGET_JAR,RESOLUTION_STATUS,"
                            + "CANDIDATES) VALUES (?,?,?,?,?,?,?,?,?,?,?)");
            methodCall = connection.prepareStatement(
                    "INSERT INTO JAVA_ASM_METHOD_CALL "
                            + "(GROUP_NAME,ORIGIN_JAR,ORIGIN_CLASS,ORIGIN_METHOD,ORIGIN_SOURCE_FILE,"
                            + "ORIGIN_LINE,OPCODE,BYTECODE_OWNER,CALLED_METHOD_NAME,CALLED_DESCRIPTOR,"
                            + "BYTECODE_CALLED_METHOD,DEFINITION_JAR,DEFINITION_CLASS,DEFINITION_METHOD,"
                            + "DEFINITION_SOURCE_FILE,DEFINITION_FIRST_LINE,DISPATCH,RESOLUTION_STATUS,"
                            + "CANDIDATES) VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)");
            classCall = connection.prepareStatement(
                    "INSERT INTO JAVA_ASM_CLASS_CALL "
                            + "(GROUP_NAME,ORIGIN_JAR,ORIGIN_CLASS,TARGET_CLASS,TARGET_JAR,"
                            + "RESOLUTION_STATUS,CANDIDATES,CALL_COUNT) VALUES (?,?,?,?,?,?,?,?)");
            adapterInherit = connection.prepareStatement(
                    "INSERT INTO JAVA_ASM_ADAPTER_INHERIT "
                            + "(GROUP_NAME,ADAPTER_JAR,ADAPTER_CLASS,INHERIT_DEPTH,SUPER_CLASS,"
                            + "SUPER_JAR,RESOLUTION_STATUS,CANDIDATES) VALUES (?,?,?,?,?,?,?,?)");
            phaseEnd("DB_CONNECT", start);
        }

        void truncateAll() {
            if (!DB_ENABLED) {
                return;
            }
            long start = phaseStart("DB_TRUNCATE");
            Statement statement = null;
            try {
                statement = connection.createStatement();
                statement.executeUpdate(
                        "TRUNCATE TABLE JAVA_ASM_PROCESSING_FLOW, JAVA_ASM_ADAPTER_INHERIT, "
                                + "JAVA_ASM_CLASS_CALL, JAVA_ASM_METHOD_CALL, JAVA_ASM_CLASS_REF, "
                                + "JAVA_ASM_METHOD_DEF, JAVA_ASM_CLASS_DEF RESTART IDENTITY");
                connection.commit();
                rowsSinceCommit = 0;
                phaseEnd("DB_TRUNCATE", start);
            } catch (SQLException e) {
                rollbackQuietly();
                throw new OutputWriteException("PostgreSQL TRUNCATE failed", e);
            } finally {
                closeQuietly(statement);
            }
        }

        void prepareProcessingFlowBulkLoad() {
            if (!DB_ENABLED) return;
            flushAndCommit();
            long start = phaseStart("DROP_PROCESSING_FLOW_INDEXES");
            Statement statement = null;
            try {
                statement = connection.createStatement();
                statement.executeUpdate("DROP INDEX IF EXISTS IDX_JAVA_ASM_PROCESSING_FLOW_ADAPTER");
                statement.executeUpdate("DROP INDEX IF EXISTS IDX_JAVA_ASM_PROCESSING_FLOW_NODE");
                statement.executeUpdate("DROP INDEX IF EXISTS IDX_JAVA_ASM_PROCESSING_FLOW_RAW_CALL");
                connection.commit();
                phaseEnd("DROP_PROCESSING_FLOW_INDEXES", start);
            } catch (SQLException e) {
                rollbackQuietly();
                throw new OutputWriteException("PostgreSQL processing-flow index drop failed", e);
            } finally {
                closeQuietly(statement);
            }
        }

        void rebuildProcessingFlowIndexes() {
            if (!DB_ENABLED) return;
            flushAndCommit();
            long start = phaseStart("CREATE_PROCESSING_FLOW_INDEXES");
            Statement statement = null;
            try {
                statement = connection.createStatement();
                statement.executeUpdate(
                        "CREATE INDEX IF NOT EXISTS IDX_JAVA_ASM_PROCESSING_FLOW_ADAPTER "
                                + "ON JAVA_ASM_PROCESSING_FLOW (GROUP_NAME, ADAPTER_CLASS, FLOW_ORDER)");
                statement.executeUpdate(
                        "CREATE INDEX IF NOT EXISTS IDX_JAVA_ASM_PROCESSING_FLOW_NODE "
                                + "ON JAVA_ASM_PROCESSING_FLOW (GROUP_NAME, NODE_CLASS)");
                statement.executeUpdate(
                        "CREATE INDEX IF NOT EXISTS IDX_JAVA_ASM_PROCESSING_FLOW_RAW_CALL "
                                + "ON JAVA_ASM_PROCESSING_FLOW (RAW_METHOD_CALL_ID) "
                                + "WHERE RAW_METHOD_CALL_ID IS NOT NULL");
                connection.commit();
                phaseEnd("CREATE_PROCESSING_FLOW_INDEXES", start);
            } catch (SQLException e) {
                rollbackQuietly();
                throw new OutputWriteException("PostgreSQL processing-flow index create failed", e);
            } finally {
                closeQuietly(statement);
            }
        }

        FlowBuildStats rebuildAllProcessingFlows() {
            if (!DB_ENABLED) {
                return new FlowBuildStats();
            }
            flushAndCommit();
            try (DbProcessingFlowOutput flow = new DbProcessingFlowOutput(connection)) {
                FlowBuildStats stats = flow.writeAllAdapters();
                log("PROCESSING_FLOW_SUMMARY adaptersScanned=" + stats.adapterCount
                        + " adaptersWithoutRoot=" + stats.adaptersWithoutRoot
                        + " roots=" + stats.rootCount + " rows=" + stats.rowCount);
                return stats;
            } catch (SQLException e) {
                throw dbFailure("PostgreSQL all-Adapter processing-flow initialization failed", e);
            } catch (IOException e) {
                throw new OutputWriteException("Processing-flow close/write failed", e);
            }
        }

        long writeFixmeMethodFlow(Path path, String adapterClass) {
            if (!DB_ENABLED) {
                return 0;
            }
            flushAndCommit();
            try (DbMethodFlowTextOutput flow = new DbMethodFlowTextOutput(connection, path)) {
                long starts = flow.writeAdapter(adapterClass);
                log("FIXME_FLOW_FILE=" + normalize(path.toString()));
                log("FIXME_FLOW_STARTS=" + starts);
                return starts;
            } catch (SQLException e) {
                throw dbFailure("PostgreSQL method-flow initialization failed", e);
            } catch (IOException e) {
                throw new OutputWriteException("Method-flow file close/write failed", e);
            }
        }

        void analyzeSourceTables() {
            if (!DB_ENABLED) {
                return;
            }
            Statement statement = null;
            try {
                flushAndCommit();
                statement = connection.createStatement();
                statement.executeUpdate("ANALYZE JAVA_ASM_CLASS_DEF");
                statement.executeUpdate("ANALYZE JAVA_ASM_METHOD_DEF");
                statement.executeUpdate("ANALYZE JAVA_ASM_CLASS_REF");
                statement.executeUpdate("ANALYZE JAVA_ASM_METHOD_CALL");
                statement.executeUpdate("ANALYZE JAVA_ASM_CLASS_CALL");
                statement.executeUpdate("ANALYZE JAVA_ASM_ADAPTER_INHERIT");
                log("DB_ANALYZE_SOURCE=DONE");
            } catch (SQLException e) {
                rollbackQuietly();
                throw new OutputWriteException("PostgreSQL source-table ANALYZE failed", e);
            } finally {
                closeQuietly(statement);
            }
        }

        void analyzeProcessingFlow() {
            if (!DB_ENABLED) {
                return;
            }
            Statement statement = null;
            try {
                flushAndCommit();
                statement = connection.createStatement();
                statement.executeUpdate("ANALYZE JAVA_ASM_PROCESSING_FLOW");
                log("DB_ANALYZE_PROCESSING_FLOW=DONE");
            } catch (SQLException e) {
                rollbackQuietly();
                throw new OutputWriteException("PostgreSQL processing-flow ANALYZE failed", e);
            } finally {
                closeQuietly(statement);
            }
        }

        void writeClassDef(ClassDef d) {
            if (!DB_ENABLED || d == null || !isOutputClassName(d.className)) return;
            try {
                int i = 1;
                classDef.setString(i++, d.group);
                classDef.setString(i++, d.jarPath);
                classDef.setString(i++, d.className);
                classDef.setString(i++, classAccessString(d.access));
                classDef.setString(i++, storedSuperClass(d));
                classDef.setString(i++, storedInterfaces(d));
                classDef.setString(i++, safe(d.sourceFile));
                classDef.setBoolean(i++, isAdapterStartClass(d.className));
                addBatchRow(classDef, DbBatchKind.CLASS_DEF, "JAVA_ASM_CLASS_DEF");
            } catch (SQLException e) {
                throw dbFailure("JAVA_ASM_CLASS_DEF insert failed jar=" + d.jarPath + " class=" + d.className, e);
            }
        }

        void writeMethodDef(ClassDef c, MethodDef m) {
            if (!DB_ENABLED || c == null || m == null || !isOutputClassName(c.className)) return;
            try {
                int i = 1;
                methodDef.setString(i++, c.group);
                methodDef.setString(i++, c.jarPath);
                methodDef.setString(i++, c.className);
                methodDef.setString(i++, m.name);
                methodDef.setString(i++, m.descriptor);
                methodDef.setString(i++, readableMethod(c.className, m.access, m.name,
                        m.descriptor, m.parameterNames));
                methodDef.setString(i++, methodAccessString(m.access));
                methodDef.setString(i++, safe(c.sourceFile));
                setNullableInt(methodDef, i++, m.firstLine);
                setNullableInt(methodDef, i++, m.lastLine);
                addBatchRow(methodDef, DbBatchKind.METHOD_DEF, "JAVA_ASM_METHOD_DEF");
            } catch (SQLException e) {
                throw dbFailure("JAVA_ASM_METHOD_DEF insert failed jar=" + c.jarPath + " class=" + c.className + " method=" + m.name + m.descriptor, e);
            }
        }

        void writeClassRef(String group, String originJar, String originClass,
                           String originMethod, String originSource, int line,
                           String kind, String targetClass, ClassResolution r) {
            if (!DB_ENABLED || !isOutputClassName(originClass)
                    || !isOutputClassName(targetClass)) return;
            try {
                int i = 1;
                classRef.setString(i++, group);
                classRef.setString(i++, originJar);
                classRef.setString(i++, originClass);
                classRef.setString(i++, originMethod);
                classRef.setString(i++, safe(originSource));
                setNullableInt(classRef, i++, line);
                classRef.setString(i++, kind);
                classRef.setString(i++, targetClass);
                classRef.setString(i++, safe(r.targetJar));
                classRef.setString(i++, safe(r.status));
                classRef.setString(i++, safe(r.candidates));
                addBatchRow(classRef, DbBatchKind.CLASS_REF, "JAVA_ASM_CLASS_REF");
            } catch (SQLException e) {
                throw dbFailure("JAVA_ASM_CLASS_REF insert failed origin=" + originClass + " target=" + targetClass + " kind=" + kind, e);
            }
        }

        void writeMethodCall(String group, String originJar, String originClass,
                             String originMethod, String originSource, int line,
                             String opcode, String bytecodeOwner, String calledName,
                             String calledDescriptor, String bytecodeReadable,
                             MethodResolution r, String dispatch) {
            if (!DB_ENABLED || !isOutputClassName(originClass)
                    || !isOutputClassName(bytecodeOwner)) return;
            r = sanitizeMethodResolutionForOutput(r);
            try {
                int i = 1;
                methodCall.setString(i++, group);
                methodCall.setString(i++, originJar);
                methodCall.setString(i++, originClass);
                methodCall.setString(i++, originMethod);
                methodCall.setString(i++, safe(originSource));
                setNullableInt(methodCall, i++, line);
                methodCall.setString(i++, opcode);
                methodCall.setString(i++, bytecodeOwner);
                methodCall.setString(i++, calledName);
                methodCall.setString(i++, calledDescriptor);
                methodCall.setString(i++, bytecodeReadable);
                methodCall.setString(i++, safe(r.definitionJar));
                methodCall.setString(i++, safe(r.definitionClass));
                methodCall.setString(i++, safe(r.definitionMethod));
                methodCall.setString(i++, safe(r.definitionSource));
                setNullableInt(methodCall, i++, r.definitionFirstLine);
                methodCall.setString(i++, dispatch);
                methodCall.setString(i++, safe(r.status));
                methodCall.setString(i++, safe(r.candidates));
                addBatchRow(methodCall, DbBatchKind.METHOD_CALL, "JAVA_ASM_METHOD_CALL");
            } catch (SQLException e) {
                throw dbFailure("JAVA_ASM_METHOD_CALL insert failed origin=" + originClass + " method=" + originMethod + " target=" + bytecodeOwner + "#" + calledName + calledDescriptor, e);
            }
        }

        void writeClassCall(ClassCallEdge e) {
            if (!DB_ENABLED || e == null || !isOutputClassName(e.originClass)
                    || !isOutputClassName(e.targetClass)) return;
            try {
                int i = 1;
                classCall.setString(i++, e.group);
                classCall.setString(i++, e.originJar);
                classCall.setString(i++, e.originClass);
                classCall.setString(i++, e.targetClass);
                classCall.setString(i++, e.targetJar);
                classCall.setString(i++, e.resolutionStatus);
                classCall.setString(i++, e.candidates);
                classCall.setLong(i++, e.callCount);
                addBatchRow(classCall, DbBatchKind.CLASS_CALL, "JAVA_ASM_CLASS_CALL");
            } catch (SQLException ex) {
                throw dbFailure("JAVA_ASM_CLASS_CALL insert failed origin=" + e.originClass + " target=" + e.targetClass, ex);
            }
        }

        void writeAdapterInherit(AdapterInheritEdge e) {
            if (!DB_ENABLED || e == null || !isAdapterStartClass(e.adapterClass)
                    || !isTargetClassName(e.superClass)) return;
            try {
                int i = 1;
                adapterInherit.setString(i++, e.group);
                adapterInherit.setString(i++, e.adapterJar);
                adapterInherit.setString(i++, e.adapterClass);
                adapterInherit.setInt(i++, e.depth);
                adapterInherit.setString(i++, e.superClass);
                adapterInherit.setString(i++, e.superJar);
                adapterInherit.setString(i++, e.resolutionStatus);
                adapterInherit.setString(i++, e.candidates);
                addBatchRow(adapterInherit, DbBatchKind.ADAPTER_INHERIT, "JAVA_ASM_ADAPTER_INHERIT");
            } catch (SQLException ex) {
                throw dbFailure("JAVA_ASM_ADAPTER_INHERIT insert failed adapter=" + e.adapterClass + " super=" + e.superClass, ex);
            }
        }

        private void addBatchRow(PreparedStatement ps, DbBatchKind kind, String table)
                throws SQLException {
            ps.addBatch();
            setBatchCount(kind, batchCount(kind) + 1);
            rowsSinceCommit++;
            if (batchCount(kind) >= DB_BATCH_SIZE) {
                executeBatch(ps, kind, table);
            }
            if (rowsSinceCommit >= DB_COMMIT_ROWS) {
                commitPending(table);
            }
        }

        private void executeBatch(PreparedStatement ps, DbBatchKind kind, String table)
                throws SQLException {
            if (batchCount(kind) <= 0) return;
            int[] results = ps.executeBatch();
            for (int result : results) {
                if (result == Statement.EXECUTE_FAILED) {
                    throw new SQLException(table + " JDBC batch reported EXECUTE_FAILED");
                }
            }
            setBatchCount(kind, 0);
        }

        private void flushBatches() throws SQLException {
            executeBatch(classDef, DbBatchKind.CLASS_DEF, "JAVA_ASM_CLASS_DEF");
            executeBatch(methodDef, DbBatchKind.METHOD_DEF, "JAVA_ASM_METHOD_DEF");
            executeBatch(classRef, DbBatchKind.CLASS_REF, "JAVA_ASM_CLASS_REF");
            executeBatch(methodCall, DbBatchKind.METHOD_CALL, "JAVA_ASM_METHOD_CALL");
            executeBatch(classCall, DbBatchKind.CLASS_CALL, "JAVA_ASM_CLASS_CALL");
            executeBatch(adapterInherit, DbBatchKind.ADAPTER_INHERIT, "JAVA_ASM_ADAPTER_INHERIT");
        }

        private int batchCount(DbBatchKind kind) {
            switch (kind) {
                case CLASS_DEF: return classDefBatch;
                case METHOD_DEF: return methodDefBatch;
                case CLASS_REF: return classRefBatch;
                case METHOD_CALL: return methodCallBatch;
                case CLASS_CALL: return classCallBatch;
                case ADAPTER_INHERIT: return adapterInheritBatch;
                default: return 0;
            }
        }

        private void setBatchCount(DbBatchKind kind, int value) {
            switch (kind) {
                case CLASS_DEF: classDefBatch = value; break;
                case METHOD_DEF: methodDefBatch = value; break;
                case CLASS_REF: classRefBatch = value; break;
                case METHOD_CALL: methodCallBatch = value; break;
                case CLASS_CALL: classCallBatch = value; break;
                case ADAPTER_INHERIT: adapterInheritBatch = value; break;
                default: break;
            }
        }

        void flushAndCommit() {
            if (!DB_ENABLED) return;
            commitPending("EXPLICIT_FLUSH");
        }

        private void commitPending(String source) {
            if (rowsSinceCommit <= 0) {
                return;
            }
            try {
                int committedRows = rowsSinceCommit;
                flushBatches();
                connection.commit();
                rowsSinceCommit = 0;
                commitCount++;
                if (commitCount % DB_COMMIT_LOG_EVERY == 0) {
                    log("DB_COMMIT source=" + source + " commitNo=" + commitCount
                            + " rows=" + committedRows + " " + memorySummary());
                }
            } catch (SQLException e) {
                rollbackQuietly();
                throw dbFailure("PostgreSQL batch commit failed", e);
            }
        }

        private static void setNullableInt(PreparedStatement ps, int index, int value)
                throws SQLException {
            if (value < 0) {
                ps.setNull(index, java.sql.Types.INTEGER);
            } else {
                ps.setInt(index, value);
            }
        }

        private OutputWriteException dbFailure(String message, SQLException e) {
            logError("ERROR " + message
                    + " sqlState=" + safe(e.getSQLState())
                    + " errorCode=" + e.getErrorCode()
                    + " message=" + safe(e.getMessage()));
            rollbackQuietly();
            return new OutputWriteException(message, e);
        }

        private void rollbackQuietly() {
            rowsSinceCommit = 0;
            classDefBatch = 0;
            methodDefBatch = 0;
            classRefBatch = 0;
            methodCallBatch = 0;
            classCallBatch = 0;
            adapterInheritBatch = 0;
            try { if (classDef != null) classDef.clearBatch(); } catch (SQLException ignored) { }
            try { if (methodDef != null) methodDef.clearBatch(); } catch (SQLException ignored) { }
            try { if (classRef != null) classRef.clearBatch(); } catch (SQLException ignored) { }
            try { if (methodCall != null) methodCall.clearBatch(); } catch (SQLException ignored) { }
            try { if (classCall != null) classCall.clearBatch(); } catch (SQLException ignored) { }
            try { if (adapterInherit != null) adapterInherit.clearBatch(); } catch (SQLException ignored) { }
            if (connection != null) {
                try { connection.rollback(); } catch (SQLException ignored) { }
            }
        }

        private enum DbBatchKind {
            CLASS_DEF, METHOD_DEF, CLASS_REF, METHOD_CALL, CLASS_CALL, ADAPTER_INHERIT
        }

        @Override
        public void close() throws IOException {
            if (!DB_ENABLED) return;
            OutputWriteException failure = null;
            try {
                flushAndCommit();
            } catch (OutputWriteException e) {
                failure = e;
            }
            closeQuietly(adapterInherit);
            closeQuietly(classCall);
            closeQuietly(methodCall);
            closeQuietly(classRef);
            closeQuietly(methodDef);
            closeQuietly(classDef);
            closeQuietly(connection);
            if (failure != null) {
                throw new IOException(failure.getMessage(), failure);
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
        private final BufferedWriter adapterInherit;
        private final Stats stats;
        private final DbOutputs db;

        CsvOutputs(Path dir, Stats stats, DbOutputs db) throws IOException {
            this.stats = stats;
            this.db = db;
            if (CSV_ENABLED) {
                classDef = newCsvWriter(dir.resolve("class_def.csv"));
                methodDef = newCsvWriter(dir.resolve("method_def.csv"));
                classRef = newCsvWriter(dir.resolve("class_ref.csv"));
                methodCall = newCsvWriter(dir.resolve("method_call.csv"));
                adapterInherit = newCsvWriter(dir.resolve("adapter_inherit.csv"));

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
                row(adapterInherit, "group", "adapter_jar", "adapter_class", "inherit_depth",
                        "super_class", "super_jar", "resolution_status", "candidates");
            } else {
                classDef = null;
                methodDef = null;
                classRef = null;
                methodCall = null;
                adapterInherit = null;
            }
        }

        synchronized void writeClassDef(ClassDef d) {
            if (d == null || !isOutputClassName(d.className)) return;
            if (CSV_ENABLED) {
                row(classDef, d.group, d.jarPath, d.className, classAccessString(d.access),
                        storedSuperClass(d), storedInterfaces(d), safe(d.sourceFile));
            }
            db.writeClassDef(d);
            stats.classDefRows++;
        }

        synchronized void writeMethodDef(ClassDef c, MethodDef m) {
            if (c == null || m == null || !isOutputClassName(c.className)) return;
            if (CSV_ENABLED) {
                row(methodDef, c.group, c.jarPath, c.className, m.name, m.descriptor,
                        readableMethod(c.className, m.access, m.name, m.descriptor, m.parameterNames),
                        methodAccessString(m.access), safe(c.sourceFile),
                        number(m.firstLine), number(m.lastLine));
            }
            db.writeMethodDef(c, m);
            stats.methodDefRows++;
        }

        synchronized void writeClassRef(String group, String originJar, String originClass,
                           String originMethod, String originSource, int line,
                           String kind, String targetClass, ClassResolution r) {
            if (!isOutputClassName(originClass) || !isOutputClassName(targetClass)) return;
            if (CSV_ENABLED) {
                row(classRef, group, originJar, originClass, originMethod, safe(originSource),
                        number(line), kind, targetClass, r.targetJar, r.status, r.candidates);
            }
            db.writeClassRef(group, originJar, originClass, originMethod, originSource,
                    line, kind, targetClass, r);
            stats.classRefRows++;
        }

        synchronized void writeMethodCall(String group, String originJar, String originClass,
                             String originMethod, String originSource, int line,
                             String opcode, String bytecodeOwner, String calledName,
                             String calledDescriptor, String bytecodeReadable,
                             MethodResolution r, String dispatch) {
            if (!isOutputClassName(originClass) || !isOutputClassName(bytecodeOwner)) return;
            r = sanitizeMethodResolutionForOutput(r);
            if (CSV_ENABLED) {
                row(methodCall, group, originJar, originClass, originMethod, safe(originSource),
                        number(line), opcode, bytecodeOwner, calledName, calledDescriptor,
                        bytecodeReadable, r.definitionJar, r.definitionClass,
                        r.definitionMethod, r.definitionSource, number(r.definitionFirstLine),
                        dispatch, r.status, r.candidates);
            }
            db.writeMethodCall(group, originJar, originClass, originMethod, originSource,
                    line, opcode, bytecodeOwner, calledName, calledDescriptor,
                    bytecodeReadable, r, dispatch);
            stats.methodCallRows++;
        }

        synchronized void writeClassCall(ClassCallEdge edge) {
            if (edge == null || !isOutputClassName(edge.originClass)
                    || !isOutputClassName(edge.targetClass)) return;
            db.writeClassCall(edge);
            stats.classCallRows++;
        }

        synchronized void writeAdapterInherit(AdapterInheritEdge edge) {
            if (edge == null || !isAdapterStartClass(edge.adapterClass)
                    || !isTargetClassName(edge.superClass)) return;
            if (CSV_ENABLED) {
                row(adapterInherit, edge.group, edge.adapterJar, edge.adapterClass,
                        Integer.toString(edge.depth), edge.superClass, edge.superJar,
                        edge.resolutionStatus, edge.candidates);
            }
            db.writeAdapterInherit(edge);
            stats.adapterInheritRows++;
        }

        synchronized void flushAndCommit() {
            db.flushAndCommit();
            try {
                if (CSV_ENABLED) {
                    classDef.flush();
                    methodDef.flush();
                    classRef.flush();
                    methodCall.flush();
                    adapterInherit.flush();
                }
            } catch (IOException e) {
                throw new OutputWriteException("CSV flush failed", e);
            }
        }

        @Override
        public synchronized void close() throws IOException {
            IOException first = null;
            if (CSV_ENABLED) {
                try { classDef.close(); } catch (IOException e) { first = e; }
                try { methodDef.close(); } catch (IOException e) { if (first == null) first = e; else first.addSuppressed(e); }
                try { classRef.close(); } catch (IOException e) { if (first == null) first = e; else first.addSuppressed(e); }
                try { methodCall.close(); } catch (IOException e) { if (first == null) first = e; else first.addSuppressed(e); }
                try { adapterInherit.close(); } catch (IOException e) { if (first == null) first = e; else first.addSuppressed(e); }
            }
            if (first != null) {
                throw first;
            }
        }
    }

    private static BufferedWriter newCsvWriter(Path path) throws IOException {
        // Large sequential output is common. A larger buffer substantially reduces write calls
        // while remaining tiny relative to an 8 GB heap.
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
            throw new OutputWriteException("CSV write failed", e);
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

    private static final class WorkerCancelledException extends RuntimeException {
        private static final long serialVersionUID = 1L;

        WorkerCancelledException() {
            super("Analysis worker interrupted");
        }
    }

    private static final class OutputWriteException extends RuntimeException {
        private static final long serialVersionUID = 1L;

        OutputWriteException(String message, Throwable cause) {
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

    /** Fast JAR-entry gate used before class bytes are read. */
    private static boolean isTargetClassEntry(JarEntry entry) {
        return isClassEntry(entry)
                && entry.getName().startsWith(TARGET_INTERNAL_PREFIX);
    }

    private static boolean isTargetInternalClassName(String internalName) {
        return internalName != null && internalName.startsWith(TARGET_INTERNAL_PREFIX);
    }

    private static boolean isTargetClassName(String className) {
        return className != null && className.startsWith(TARGET_PACKAGE_PREFIX);
    }

    private static boolean isOutputInternalClassName(String internalName) {
        return isOutputClassName(internalToClass(internalName));
    }

    /** Result/call-data rule from the user requirements. */
    private static boolean isOutputClassName(String className) {
        return isTargetClassName(className)
                && !isExcludedFrameworkClassName(className)
                && !isExceptionClassName(className);
    }

    private static boolean isExcludedFrameworkClassName(String className) {
        return className != null && className.startsWith(EXCLUDED_FRAMEWORK_PREFIX);
    }

    /**
     * Flow-only visibility rule requested for the JavaScript/sequence-diagram preparation.
     * Raw ASM tables keep their existing scope; only the temporary flow presentation suppresses
     * framework/util/Bean/Exception noise.
     */
    private static boolean isFlowVisibleClassName(String className) {
        if (!isTargetClassName(className)) {
            return false;
        }
        String normalized = className == null ? "" : className;
        if (normalized.contains(".framework.") || normalized.contains(".util.")) {
            return false;
        }
        if (normalized.contains(FLOW_EXCLUDED_CLASS_TOKEN)) {
            return false;
        }
        return !hasNestedSimpleNameSuffix(normalized, "Bean")
                && !hasNestedSimpleNameSuffix(normalized, "Exception");
    }

    /** Applies all flow-edge display rules to both caller and callee. */
    private static boolean isFlowVisibleCall(FlowMethodKey origin, FlowCall call,
                                             String targetClass) {
        if (origin == null || call == null) {
            return false;
        }
        if (!isFlowVisibleClassName(origin.className) || !isFlowVisibleClassName(targetClass)) {
            return false;
        }

        String calledName = safe(call.calledMethodName);
        if ("<init>".equals(calledName)) {
            return false;
        }
        if ("close".equals(calledName)) {
            return false;
        }
        return calledName.indexOf("Bean") < 0;
    }

    private static boolean hasNestedSimpleNameSuffix(String className, String suffix) {
        if (className == null || className.length() == 0 || suffix == null) {
            return false;
        }
        int dot = className.lastIndexOf('.');
        String simple = dot >= 0 ? className.substring(dot + 1) : className;
        int start = 0;
        while (start <= simple.length()) {
            int dollar = simple.indexOf('$', start);
            int end = dollar >= 0 ? dollar : simple.length();
            if (end > start && simple.substring(start, end).endsWith(suffix)) {
                return true;
            }
            if (dollar < 0) {
                break;
            }
            start = dollar + 1;
        }
        return false;
    }

    /** Excludes FooException, FooException$1, and Bar$InnerException-style classes. */
    private static boolean isExceptionClassName(String className) {
        return hasNestedSimpleNameSuffix(className, "Exception");
    }

    private static String storedSuperClass(ClassDef d) {
        return isOutputClassName(d.superClassName) ? d.superClassName : "";
    }

    private static String storedInterfaces(ClassDef d) {
        List<String> allowed = new ArrayList<String>();
        for (String intf : d.interfaces) {
            if (isOutputClassName(intf)) {
                allowed.add(intf);
            }
        }
        return join(allowed, ";");
    }

    private static MethodResolution sanitizeMethodResolutionForOutput(MethodResolution r) {
        if (r == null) {
            return MethodResolution.notFound(NOT_FOUND_IN_GROUP);
        }
        if (r.definitionClass.length() > 0 && !isOutputClassName(r.definitionClass)) {
            // The symbolic owner is allowed, but its implementation was inherited from an
            // excluded framework/Exception class. Do not leak excluded data into PostgreSQL/CSV.
            return MethodResolution.notFound(NOT_FOUND_IN_GROUP);
        }
        return r;
    }

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
            stats.skippedClassEntries.incrementAndGet();
            logError("WARN CLASS_TOO_LARGE " + info.relativePath + "!"
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
                        stats.skippedClassEntries.incrementAndGet();
                        logError("WARN TRUNCATED_CLASS " + info.relativePath + "!"
                                + entry.getName() + " expected=" + declared + " actual=" + offset);
                        return null;
                    }
                    if (n == 0) {
                        int one = in.read();
                        if (one < 0) {
                            stats.skippedClassEntries.incrementAndGet();
                            logError("WARN TRUNCATED_CLASS " + info.relativePath + "!"
                                    + entry.getName() + " expected=" + declared + " actual=" + offset);
                            return null;
                        }
                        bytes[offset++] = (byte) one;
                    } else {
                        offset += n;
                    }
                }

                if (in.read() != -1) {
                    stats.skippedClassEntries.incrementAndGet();
                    logError("WARN CLASS_SIZE_MISMATCH " + info.relativePath + "!"
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
                    stats.skippedClassEntries.incrementAndGet();
                    logError("WARN CLASS_TOO_LARGE " + info.relativePath + "!"
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
            stats.skippedClassEntries.incrementAndGet();
            warn("READ_CLASS", info, entry, e);
            return null;
        } catch (RuntimeException e) {
            stats.skippedClassEntries.incrementAndGet();
            warn("READ_CLASS", info, entry, e);
            return null;
        } finally {
            closeQuietly(in);
        }
    }

    // ---------------------------------------------------------------------
    // Model
    // ---------------------------------------------------------------------

    private static final class MigrationWork {
        final String name;
        final List<GroupWork> groups;
        final int jarCount;

        MigrationWork(String name, List<GroupWork> groups) {
            this.name = safe(name);
            this.groups = groups;
            int count = 0;
            for (GroupWork group : groups) {
                count += group.jars.size();
            }
            this.jarCount = count;
        }
    }

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

    private static final class AdapterInheritEdge implements Comparable<AdapterInheritEdge> {
        String group = "";
        String adapterJar = "";
        String adapterClass = "";
        int depth;
        String superClass = "";
        String superJar = "";
        String resolutionStatus = "";
        String candidates = "";

        @Override
        public int compareTo(AdapterInheritEdge other) {
            int c = adapterJar.compareTo(other.adapterJar);
            if (c != 0) return c;
            c = adapterClass.compareTo(other.adapterClass);
            if (c != 0) return c;
            return depth < other.depth ? -1 : (depth == other.depth ? 0 : 1);
        }
    }

    private static final class Stats {
        long classDefRows;
        long methodDefRows;
        long classRefRows;
        long methodCallRows;
        long classCallRows;
        long adapterInheritRows;
        long flowAdaptersScanned;
        long flowAdaptersWithoutRoot;
        long flowStarts;
        long processingFlowRows;
        final AtomicLong skippedClassEntries = new AtomicLong();
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
        String modifiers = methodAccessString(access);
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

    /**
     * Class and method access flags must be formatted separately.
     * Several JVM access bits intentionally have different meanings by context
     * (for example ACC_SUPER == ACC_SYNCHRONIZED).
     */
    private static String classAccessString(int access) {
        List<String> x = new ArrayList<String>();
        if ((access & Opcodes.ACC_PUBLIC) != 0) x.add("public");
        if ((access & Opcodes.ACC_PROTECTED) != 0) x.add("protected");
        if ((access & Opcodes.ACC_PRIVATE) != 0) x.add("private");
        if ((access & Opcodes.ACC_FINAL) != 0) x.add("final");
        if ((access & ACC_SUPER_FLAG) != 0) x.add("super");
        if ((access & Opcodes.ACC_INTERFACE) != 0) x.add("interface");
        if ((access & Opcodes.ACC_ABSTRACT) != 0) x.add("abstract");
        if ((access & ACC_SYNTHETIC_FLAG) != 0) x.add("synthetic");
        if ((access & ACC_ANNOTATION_FLAG) != 0) x.add("annotation");
        if ((access & ACC_ENUM_FLAG) != 0) x.add("enum");
        return join(x, " ");
    }

    private static String methodAccessString(int access) {
        List<String> x = new ArrayList<String>();
        if ((access & Opcodes.ACC_PUBLIC) != 0) x.add("public");
        if ((access & Opcodes.ACC_PROTECTED) != 0) x.add("protected");
        if ((access & Opcodes.ACC_PRIVATE) != 0) x.add("private");
        if ((access & Opcodes.ACC_ABSTRACT) != 0) x.add("abstract");
        if ((access & Opcodes.ACC_STATIC) != 0) x.add("static");
        if ((access & Opcodes.ACC_FINAL) != 0) x.add("final");
        if ((access & Opcodes.ACC_SYNCHRONIZED) != 0) x.add("synchronized");
        if ((access & ACC_BRIDGE_FLAG) != 0) x.add("bridge");
        if ((access & ACC_VARARGS_FLAG) != 0) x.add("varargs");
        if ((access & Opcodes.ACC_NATIVE) != 0) x.add("native");
        if ((access & Opcodes.ACC_STRICT) != 0) x.add("strictfp");
        if ((access & ACC_SYNTHETIC_FLAG) != 0) x.add("synthetic");
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

    // ---------------------------------------------------------------------
    // Timestamped logging / heap-pressure protection
    // ---------------------------------------------------------------------

    private static final Object LOG_LOCK = new Object();
    private static final Object MEMORY_RELIEF_LOCK = new Object();
    private static final SimpleDateFormat LOG_TIMESTAMP_FORMAT =
            new SimpleDateFormat("yyyy-MM-dd HH:mm:ss.SSS", Locale.ROOT);

    private static void log(String message) {
        synchronized (LOG_LOCK) {
            System.out.println("[" + timestampUnsafe() + "]"
                    + " [" + Thread.currentThread().getName() + "] "
                    + safe(message));
        }
    }

    private static void logError(String message) {
        synchronized (LOG_LOCK) {
            System.err.println("[" + timestampUnsafe() + "]"
                    + " [" + Thread.currentThread().getName() + "] "
                    + safe(message));
        }
    }

    private static String timestampUnsafe() {
        return LOG_TIMESTAMP_FORMAT.format(new Date());
    }

    private static long phaseStart(String label) {
        log("START " + label + " " + memorySummary());
        return System.nanoTime();
    }

    private static void phaseEnd(String label, long startNanos) {
        log("END " + label + " elapsed=" + formatElapsed(startNanos)
                + " " + memorySummary());
    }

    private static String formatElapsed(long startNanos) {
        long elapsedNanos = System.nanoTime() - startNanos;
        long millis = elapsedNanos / 1000000L;
        long hours = millis / 3600000L;
        long minutes = (millis % 3600000L) / 60000L;
        long seconds = (millis % 60000L) / 1000L;
        long remainMillis = millis % 1000L;
        return String.format(Locale.ROOT, "%02d:%02d:%02d.%03d",
                Long.valueOf(hours), Long.valueOf(minutes),
                Long.valueOf(seconds), Long.valueOf(remainMillis));
    }

    private static long mb(long bytes) {
        return bytes / (1024L * 1024L);
    }

    private static String memorySummary() {
        Runtime rt = Runtime.getRuntime();
        long max = rt.maxMemory();
        long committed = rt.totalMemory();
        long freeInsideCommitted = rt.freeMemory();
        long used = committed - freeInsideCommitted;
        long headroom = Math.max(0L, max - used);
        long percent = max <= 0L ? 0L : (used * 100L / max);
        return "heapUsedMB=" + mb(used)
                + " heapCommittedMB=" + mb(committed)
                + " heapMaxMB=" + mb(max)
                + " heapHeadroomMB=" + mb(headroom)
                + " heapUsedPct=" + percent;
    }

    /**
     * Invoked only at safe boundaries where transient class/JAR/flow allocations are no longer
     * needed. It never discards the current directory group's class index, which is required for
     * correct method resolution.
     */
    private static void memoryCheckpoint(String reason, MethodResolver resolver, boolean forceGc) {
        Runtime rt = Runtime.getRuntime();
        long max = rt.maxMemory();
        long used = rt.totalMemory() - rt.freeMemory();
        long headroom = Math.max(0L, max - used);
        long thresholdBytes = max * (long) MEMORY_GC_THRESHOLD_PERCENT / 100L;
        boolean pressure = used >= thresholdBytes
                || headroom <= MEMORY_MIN_HEADROOM_MB * 1024L * 1024L;

        if (!pressure) {
            return;
        }

        // With three analysis workers, prevent simultaneous full-GC requests from causing a GC storm.
        synchronized (MEMORY_RELIEF_LOCK) {
            rt = Runtime.getRuntime();
            max = rt.maxMemory();
            used = rt.totalMemory() - rt.freeMemory();
            headroom = Math.max(0L, max - used);
            thresholdBytes = max * (long) MEMORY_GC_THRESHOLD_PERCENT / 100L;
            pressure = used >= thresholdBytes
                    || headroom <= MEMORY_MIN_HEADROOM_MB * 1024L * 1024L;
            if (!pressure) {
                return;
            }

            int cleared = resolver == null ? 0 : resolver.clearCache();
            log("MEMORY_RELIEF_START reason=" + reason
                    + " pressure=true"
                    + " resolverCacheCleared=" + cleared
                    + " " + memorySummary());
            System.gc();
            log("MEMORY_RELIEF_END reason=" + reason + " " + memorySummary());
        }
    }

    private static void warn(String kind, JarInfo jar, JarEntry entry, Throwable t) {
        String where = jar == null ? "" : jar.relativePath;
        if (entry != null) {
            where += "!" + entry.getName();
        }
        logError("WARN " + kind + " " + where + " : "
                + t.getClass().getName() + ": " + safe(t.getMessage()));
    }

    private static void closeQuietly(Object obj) {
        if (obj == null) {
            return;
        }
        try {
            if (obj instanceof AutoCloseable) {
                ((AutoCloseable) obj).close();
            }
        } catch (Exception ignored) {
            // no-op
        }
    }
}


