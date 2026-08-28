import java.io.BufferedInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.Reader;
import java.io.StringReader;
import java.io.OutputStream;
import java.net.CookieHandler;
import java.net.CookieManager;
import java.net.CookiePolicy;
import java.net.HttpURLConnection;
import java.net.URL;
import java.net.URLEncoder;
import java.nio.charset.Charset;
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
import java.util.ArrayList;
import java.util.Collections;
import java.util.Enumeration;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Properties;
import java.util.Set;
import java.util.TreeSet;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.zip.ZipEntry;
import java.util.zip.ZipException;
import java.util.zip.ZipFile;

public class Main {

    private static final String DEFAULT_BASE_DIR =
            "/home/aiuser/nkSec/tools/iko-rsync-main/IKO/Master/nikkoEZ/";
    private static final String DEFAULT_BASE_URL =
            "http://10.202.6.34/BatchSupportSiteManager";
    private static final String DEFAULT_DB_URL =
            "jdbc:postgresql://10.205.7.19:5432/postgres";
    private static final String DEFAULT_DB_USER = "postgres";
    private static final String DEFAULT_DB_PASSWORD = "postgres";

    private static final String SYSTEM_NAME = "ez.web.online";
    private static final String EXCLUDED_TABLE_NAME = "BatchQuery";
    private static final Charset DEFAULT_RESPONSE_CHARSET = Charset.forName("MS932");

    private static final int DEFAULT_CONNECT_TIMEOUT_MS = 10000;
    private static final int DEFAULT_READ_TIMEOUT_MS = 60000;
    private static final int DEFAULT_BATCH_ROWS = 500;
    private static final int DEFAULT_COMMIT_ADAPTERS = 100;
    private static final int DEFAULT_PROGRESS_ADAPTERS = 100;

    private static final Pattern TARGET_CELL_PATTERN = Pattern.compile(
            "(?is)<td\\b[^>]*\\btargetId\\s*=\\s*[\"']([^\"']+)[\"'][^>]*>(.*?)</td\\s*>");
    private static final Pattern CHARSET_PATTERN = Pattern.compile(
            "(?i)charset\\s*=\\s*[\"']?([^;\"'\\s]+)");
    private static final Pattern COUNT_TH_PATTERN = Pattern.compile(
            "(?is)<th\\b[^>]*class\\s*=\\s*[\"'][^\"']*count_style[^\"']*[\"'][^>]*>(.*?)</th\\s*>");
    private static final Pattern DIGIT_PATTERN = Pattern.compile("([0-9,]+)");

    public static void main(String[] args) {
        long started = System.currentTimeMillis();
        Config config = Config.load();

        try {
            System.out.println("[START] Adapter scan: " + config.baseDir);
            ScanResult scan = findAdapterClassNames(config.baseDir);
            List<String> adapters = new ArrayList<String>(scan.adapterNames);
            Collections.sort(adapters);

            System.out.println("[SCAN] adapters=" + adapters.size()
                    + ", archives=" + scan.archiveCount
                    + ", unreadableArchives=" + scan.unreadableArchiveCount);

            if (adapters.isEmpty()) {
                throw new IllegalStateException("Adapter class was not found under: " + config.baseDir);
            }

            Class.forName("org.postgresql.Driver");
            CookieManager cookieManager = new CookieManager(null, CookiePolicy.ACCEPT_ALL);
            CookieHandler.setDefault(cookieManager);

            HttpClient http = new HttpClient(config, cookieManager);
            http.initializeSession();

            Properties dbProperties = new Properties();
            dbProperties.setProperty("user", config.dbUser);
            dbProperties.setProperty("password", config.dbPassword);
            dbProperties.setProperty("reWriteBatchedInserts", "true");
            dbProperties.setProperty("ApplicationName", "CRUD-EZ-Collector");

            try (Connection connection = DriverManager.getConnection(
                    config.dbUrl, dbProperties)) {
                connection.setAutoCommit(false);
                verifyTargetTables(connection);
                createTemporaryStagingTables(connection);
                connection.commit();

                BatchInserter inserter = new BatchInserter(connection, config.batchRows);
                long rowCount1 = 0L;
                long rowCount2 = 0L;

                try {
                    int processed = 0;
                    for (String adapterName : adapters) {
                        SearchStats stats = http.search(adapterName, inserter);
                        rowCount1 += stats.headerRows;
                        rowCount2 += stats.crudRows;

                        processed++;
                        if (processed % config.commitAdapters == 0) {
                            inserter.flush();
                            connection.commit();
                        }
                        if (processed % config.progressAdapters == 0 || processed == adapters.size()) {
                            System.out.println("[PROGRESS] " + processed + "/" + adapters.size()
                                    + " adapters, headerRows=" + rowCount1
                                    + ", crudRows=" + rowCount2);
                        }
                    }

                    inserter.flush();
                    connection.commit();
                    inserter.close();

                    publishSnapshot(connection);
                    connection.commit();
                } catch (Exception e) {
                    rollbackQuietly(connection);
                    throw e;
                } finally {
                    inserter.closeQuietly();
                }

                long finalCount1 = countRows(connection, "CRUD_ONLINE_EZ1");
                long finalCount2 = countRows(connection, "CRUD_ONLINE_EZ2");
                System.out.println("[DB] CRUD_ONLINE_EZ1=" + finalCount1
                        + ", CRUD_ONLINE_EZ2=" + finalCount2);
            }

            long elapsed = System.currentTimeMillis() - started;
            System.out.println("[END] elapsedMs=" + elapsed);
        } catch (Exception e) {
            System.err.println("[ERROR] " + e.getClass().getName() + ": " + e.getMessage());
            e.printStackTrace(System.err);
            System.exit(1);
        }
    }

    static ScanResult findAdapterClassNames(Path baseDir) throws IOException {
        if (!Files.isDirectory(baseDir)) {
            throw new IOException("Base directory does not exist or is not a directory: " + baseDir);
        }

        final Set<String> adapterNames = new TreeSet<String>();
        final AtomicInteger archiveCount = new AtomicInteger();
        final AtomicInteger unreadableArchiveCount = new AtomicInteger();

        Files.walkFileTree(baseDir, new SimpleFileVisitor<Path>() {
            @Override
            public FileVisitResult visitFile(Path file, BasicFileAttributes attrs) {
                if (!attrs.isRegularFile() || !isArchiveName(file.getFileName().toString())) {
                    return FileVisitResult.CONTINUE;
                }

                archiveCount.incrementAndGet();
                try (ZipFile zip = new ZipFile(file.toFile())) {
                    Enumeration<? extends ZipEntry> entries = zip.entries();
                    while (entries.hasMoreElements()) {
                        ZipEntry entry = entries.nextElement();
                        if (entry.isDirectory()) {
                            continue;
                        }
                        String entryName = entry.getName();
                        if (!entryName.endsWith("Adapter.class")) {
                            continue;
                        }

                        int slash = entryName.lastIndexOf('/');
                        String simpleFileName = slash >= 0 ? entryName.substring(slash + 1) : entryName;
                        if (simpleFileName.indexOf('$') >= 0 || !simpleFileName.endsWith(".class")) {
                            continue;
                        }
                        String simpleClassName = simpleFileName.substring(0, simpleFileName.length() - 6);
                        if (!simpleClassName.isEmpty()) {
                            adapterNames.add(simpleClassName);
                        }
                    }
                } catch (ZipException e) {
                    unreadableArchiveCount.incrementAndGet();
                    System.err.println("[WARN] Invalid ZIP/JAR skipped: " + file + " : " + e.getMessage());
                } catch (IOException e) {
                    unreadableArchiveCount.incrementAndGet();
                    System.err.println("[WARN] Archive read failed: " + file + " : " + e.getMessage());
                }
                return FileVisitResult.CONTINUE;
            }

            @Override
            public FileVisitResult visitFileFailed(Path file, IOException exc) {
                System.err.println("[WARN] File access failed: " + file + " : " + exc.getMessage());
                return FileVisitResult.CONTINUE;
            }
        });

        return new ScanResult(adapterNames, archiveCount.get(), unreadableArchiveCount.get());
    }

    private static boolean isArchiveName(String name) {
        String lower = name.toLowerCase(Locale.ROOT);
        return lower.endsWith(".jar")
                || lower.endsWith(".zip")
                || lower.endsWith(".war")
                || lower.endsWith(".ear");
    }

    static ParsedResult parseSearchHtml(String html) throws IOException {
        if (html == null || html.isEmpty()) {
            throw new IOException("Empty HTML response");
        }

        CollectingRowSink sink = new CollectingRowSink(Integer.MAX_VALUE);
        SearchStats stats;
        try {
            stats = parseSearchHtml(new StringReader(html), sink);
        } catch (SQLException e) {
            throw new IOException("Unexpected SQL error while parsing in-memory HTML", e);
        }
        if (!stats.validPage) {
            throw new IOException("Unexpected HTML response. Search page marker was not found.");
        }
        return new ParsedResult(sink.headers, sink.cruds);
    }

    static SearchStats parseSearchHtml(Reader reader, RowSink sink) throws IOException, SQLException {
        if (reader == null) {
            throw new IOException("Empty HTML response");
        }
        StreamingHtmlParser parser = new StreamingHtmlParser(sink);
        char[] chunk = new char[8192];
        int read;
        while ((read = reader.read(chunk)) >= 0) {
            if (read > 0) {
                parser.accept(chunk, read);
            }
        }
        return parser.finish();
    }

    private static void parseRowHtml(String rowHtml, RowSink sink, SearchStats stats)
            throws IOException, SQLException {
        CellValues cells = extractTargetCells(rowHtml);
        if (!cells.hasAny) {
            return;
        }

        if (cells.adapter != null && !cells.adapter.isEmpty()) {
            stats.current = new CommonValues(
                    SYSTEM_NAME,
                    valueOrEmpty(cells.baseDate),
                    valueOrEmpty(cells.url),
                    cells.adapter,
                    valueOrEmpty(cells.screenName),
                    valueOrEmpty(cells.jspName));

            sink.addHeader(new HeaderRow(
                    stats.current.systemName,
                    stats.current.baseDate,
                    stats.current.urlMessageId,
                    stats.current.adapter,
                    stats.current.screenName,
                    stats.current.jspName));
            stats.headerRows++;
        }

        if (cells.hasTableName) {
            if (stats.current == null) {
                throw new IOException("CRUD row was found before Adapter header row");
            }
            String tableName = valueOrEmpty(cells.tableName).trim();
            if (isTargetCrudTable(tableName)) {
                sink.addCrud(new CrudRow(
                        stats.current.systemName,
                        stats.current.adapter,
                        tableName,
                        isCrudEnabled(cells.createFlag),
                        isCrudEnabled(cells.readFlag),
                        isCrudEnabled(cells.updateFlag),
                        isCrudEnabled(cells.deleteFlag)));
                stats.crudRows++;
            }
        }
    }

    private static CellValues extractTargetCells(String rowHtml) {
        CellValues values = new CellValues();
        Matcher matcher = TARGET_CELL_PATTERN.matcher(rowHtml);
        while (matcher.find()) {
            values.hasAny = true;
            String targetId = matcher.group(1);
            String value = cleanHtmlText(matcher.group(2));
            if ("adapter".equals(targetId)) {
                values.adapter = value;
            } else if ("basedate".equals(targetId)) {
                values.baseDate = value;
            } else if ("url".equals(targetId)) {
                values.url = value;
            } else if ("gamenName".equals(targetId)) {
                values.screenName = value;
            } else if ("jspName".equals(targetId)) {
                values.jspName = value;
            } else if ("tableSidPblshC".equals(targetId)) {
                values.hasTableName = true;
                values.tableName = value;
            } else if ("crudJohoCF".equals(targetId)) {
                values.createFlag = value;
            } else if ("crudJohoRF".equals(targetId)) {
                values.readFlag = value;
            } else if ("crudJohoUF".equals(targetId)) {
                values.updateFlag = value;
            } else if ("crudJohoDF".equals(targetId)) {
                values.deleteFlag = value;
            }
        }
        return values;
    }

    private static String cleanHtmlText(String html) {
        if (html == null || html.isEmpty()) {
            return "";
        }
        StringBuilder out = new StringBuilder(Math.min(html.length(), 256));
        boolean pendingSpace = false;

        for (int i = 0; i < html.length();) {
            char ch = html.charAt(i);
            if (ch == '<') {
                int close = html.indexOf('>', i + 1);
                if (close < 0) {
                    break;
                }
                int nameStart = i + 1;
                while (nameStart < close && Character.isWhitespace(html.charAt(nameStart))) {
                    nameStart++;
                }
                if (nameStart < close && html.charAt(nameStart) == '/') {
                    nameStart++;
                }
                if (regionMatchesAsciiIgnoreCase(html, nameStart, "br")) {
                    pendingSpace = out.length() > 0;
                }
                i = close + 1;
                continue;
            }

            if (ch == '&') {
                int semi = html.indexOf(';', i + 1);
                if (semi > i && semi - i <= 16) {
                    String entity = html.substring(i + 1, semi);
                    int codePoint = decodeHtmlEntityCodePoint(entity);
                    if (codePoint >= 0) {
                        if (Character.isWhitespace(codePoint) || codePoint == 0x3000) {
                            pendingSpace = out.length() > 0;
                        } else {
                            if (pendingSpace && out.length() > 0) {
                                out.append(' ');
                            }
                            pendingSpace = false;
                            out.appendCodePoint(codePoint);
                        }
                        i = semi + 1;
                        continue;
                    }
                }
            }

            if (Character.isWhitespace(ch) || ch == '\u3000') {
                pendingSpace = out.length() > 0;
            } else {
                if (pendingSpace && out.length() > 0) {
                    out.append(' ');
                }
                pendingSpace = false;
                out.append(ch);
            }
            i++;
        }
        return out.toString();
    }

    private static int decodeHtmlEntityCodePoint(String entity) {
        if ("nbsp".equals(entity)) return ' ';
        if ("amp".equals(entity)) return '&';
        if ("lt".equals(entity)) return '<';
        if ("gt".equals(entity)) return '>';
        if ("quot".equals(entity)) return '"';
        if ("apos".equals(entity) || "#39".equals(entity)) return '\'';
        if (entity.startsWith("#x") || entity.startsWith("#X")) {
            try {
                int codePoint = Integer.parseInt(entity.substring(2), 16);
                return Character.isValidCodePoint(codePoint) ? codePoint : -1;
            } catch (RuntimeException ignored) {
                return -1;
            }
        }
        if (entity.startsWith("#")) {
            try {
                int codePoint = Integer.parseInt(entity.substring(1), 10);
                return Character.isValidCodePoint(codePoint) ? codePoint : -1;
            } catch (RuntimeException ignored) {
                return -1;
            }
        }
        return -1;
    }

    private static boolean regionMatchesAsciiIgnoreCase(String text, int offset, String expected) {
        if (offset < 0 || offset + expected.length() > text.length()) {
            return false;
        }
        return text.regionMatches(true, offset, expected, 0, expected.length());
    }

    private static int indexOfIgnoreCase(StringBuilder text, String target, int fromIndex) {
        int max = text.length() - target.length();
        for (int i = Math.max(0, fromIndex); i <= max; i++) {
            boolean match = true;
            for (int j = 0; j < target.length(); j++) {
                char a = text.charAt(i + j);
                char b = target.charAt(j);
                if (a == b) {
                    continue;
                }
                if (Character.toLowerCase(a) != Character.toLowerCase(b)) {
                    match = false;
                    break;
                }
            }
            if (match) {
                return i;
            }
        }
        return -1;
    }

    private static int indexOfTagToken(StringBuilder text, String token, int fromIndex) {
        int pos = fromIndex;
        while (true) {
            pos = indexOfIgnoreCase(text, token, pos);
            if (pos < 0) {
                return -1;
            }
            int next = pos + token.length();
            if (next >= text.length()) {
                return pos;
            }
            char ch = text.charAt(next);
            if (ch == '>' || ch == '/' || Character.isWhitespace(ch)) {
                return pos;
            }
            pos++;
        }
    }

    static final class StreamingHtmlParser {
        private static final int MAX_ROW_CHARS = 8 * 1024 * 1024;
        private static final int META_WINDOW_CHARS = 64 * 1024;
        private static final int ROW_TAIL_CHARS = 16;

        private final RowSink sink;
        private final SearchStats stats = new SearchStats();
        private final StringBuilder rowBuffer = new StringBuilder(16384);
        private final StringBuilder metaWindow = new StringBuilder(16384);

        StreamingHtmlParser(RowSink sink) {
            this.sink = sink;
        }

        void accept(char[] chars, int length) throws IOException, SQLException {
            rowBuffer.append(chars, 0, length);
            metaWindow.append(chars, 0, length);
            inspectMetadata();
            processRows(false);
        }

        SearchStats finish() throws IOException, SQLException {
            inspectMetadata();
            processRows(true);
            stats.validPage = stats.hasCommandMarker && stats.hasTitleMarker;
            return stats;
        }

        private void inspectMetadata() {
            if (!stats.hasCommandMarker && indexOfIgnoreCase(metaWindow, "ezSearchRealCrudCmdInOut", 0) >= 0) {
                stats.hasCommandMarker = true;
            }
            if (!stats.hasTitleMarker && metaWindow.indexOf("EZ・リアルCRUD") >= 0) {
                stats.hasTitleMarker = true;
            }
            if (stats.resultCount < 0) {
                Matcher thMatcher = COUNT_TH_PATTERN.matcher(metaWindow);
                while (thMatcher.find()) {
                    String text = cleanHtmlText(thMatcher.group(1));
                    Matcher digitMatcher = DIGIT_PATTERN.matcher(text);
                    if (digitMatcher.find()) {
                        String digits = digitMatcher.group(1).replace(",", "");
                        try {
                            stats.resultCount = Integer.parseInt(digits);
                        } catch (NumberFormatException ignored) {
                            stats.resultCount = -1;
                        }
                        break;
                    }
                }
            }

            if (metaWindow.length() > META_WINDOW_CHARS) {
                metaWindow.delete(0, metaWindow.length() - META_WINDOW_CHARS);
            }
        }

        private void processRows(boolean endOfInput) throws IOException, SQLException {
            while (true) {
                int rowStart = indexOfTagToken(rowBuffer, "<tr", 0);
                if (rowStart < 0) {
                    if (rowBuffer.length() > ROW_TAIL_CHARS) {
                        rowBuffer.delete(0, rowBuffer.length() - ROW_TAIL_CHARS);
                    }
                    return;
                }
                if (rowStart > 0) {
                    rowBuffer.delete(0, rowStart);
                }

                int tagEnd = rowBuffer.indexOf(">");
                if (tagEnd < 0) {
                    ensureRowBounded();
                    return;
                }

                int rowEnd = indexOfTagToken(rowBuffer, "</tr", tagEnd + 1);
                if (rowEnd < 0) {
                    int nextRow = indexOfTagToken(rowBuffer, "<tr", tagEnd + 1);
                    if (nextRow >= 0) {
                        parseRowHtml(rowBuffer.substring(tagEnd + 1, nextRow), sink, stats);
                        rowBuffer.delete(0, nextRow);
                        continue;
                    }
                    if (endOfInput) {
                        parseRowHtml(rowBuffer.substring(tagEnd + 1), sink, stats);
                        rowBuffer.setLength(0);
                        return;
                    }
                    ensureRowBounded();
                    return;
                }

                int closeEnd = rowBuffer.indexOf(">", rowEnd + 4);
                if (closeEnd < 0) {
                    if (endOfInput) {
                        closeEnd = rowBuffer.length() - 1;
                    } else {
                        ensureRowBounded();
                        return;
                    }
                }

                parseRowHtml(rowBuffer.substring(tagEnd + 1, rowEnd), sink, stats);
                rowBuffer.delete(0, closeEnd + 1);
            }
        }

        private void ensureRowBounded() throws IOException {
            if (rowBuffer.length() > MAX_ROW_CHARS) {
                throw new IOException("HTML row exceeded streaming safety limit: " + MAX_ROW_CHARS + " chars");
            }
        }
    }

    private static boolean isCrudEnabled(String value) {
        if (value == null) {
            return false;
        }
        String v = value.trim();
        return "○".equals(v)
                || "〇".equals(v)
                || "1".equals(v)
                || "true".equalsIgnoreCase(v)
                || "on".equalsIgnoreCase(v)
                || "yes".equalsIgnoreCase(v);
    }

    private static String valueOrEmpty(String value) {
        return value == null ? "" : value;
    }

    private static boolean isTargetCrudTable(String tableName) {
        if (tableName == null) {
            return false;
        }
        String value = tableName.trim();
        return !value.isEmpty()
                && !"-".equals(value)
                && !EXCLUDED_TABLE_NAME.equalsIgnoreCase(value);
    }

    private static void verifyTargetTables(Connection connection) throws SQLException {
        verifyTargetTable(connection, "crud_online_ez1");
        verifyTargetTable(connection, "crud_online_ez2");
    }

    private static void verifyTargetTable(Connection connection, String tableName) throws SQLException {
        String sql = "SELECT to_regclass(?)";
        try (PreparedStatement ps = connection.prepareStatement(sql)) {
            ps.setString(1, tableName);
            try (ResultSet rs = ps.executeQuery()) {
                if (!rs.next() || rs.getString(1) == null) {
                    throw new SQLException("Target table does not exist: " + tableName
                            + ". Execute CRUD_EZ.ddl first.");
                }
            }
        }
    }

    private static void createTemporaryStagingTables(Connection connection) throws SQLException {
        try (Statement st = connection.createStatement()) {
            st.execute("DROP TABLE IF EXISTS stg_crud_online_ez2");
            st.execute("DROP TABLE IF EXISTS stg_crud_online_ez1");

            st.execute("CREATE TEMP TABLE stg_crud_online_ez1 ("
                    + "system_name VARCHAR(100) NOT NULL, "
                    + "base_date VARCHAR(20), "
                    + "url_message_id VARCHAR(400), "
                    + "adapter VARCHAR(1000) NOT NULL, "
                    + "screen_name VARCHAR(1000), "
                    + "jsp_name VARCHAR(1000)"
                    + ") ON COMMIT PRESERVE ROWS");

            st.execute("CREATE TEMP TABLE stg_crud_online_ez2 ("
                    + "system_name VARCHAR(100) NOT NULL, "
                    + "adapter VARCHAR(1000) NOT NULL, "
                    + "table_name VARCHAR(500) NOT NULL, "
                    + "create_flag BOOLEAN NOT NULL, "
                    + "read_flag BOOLEAN NOT NULL, "
                    + "update_flag BOOLEAN NOT NULL, "
                    + "delete_flag BOOLEAN NOT NULL"
                    + ") ON COMMIT PRESERVE ROWS");
        }
    }

    private static void publishSnapshot(Connection connection) throws SQLException {
        try (Statement st = connection.createStatement()) {
            // This collector scans the complete EZ target set on every run.
            // Replace the previous snapshot so stale rows (for example BatchQuery) cannot survive.
            st.executeUpdate("DELETE FROM CRUD_ONLINE_EZ2");
            st.executeUpdate("DELETE FROM CRUD_ONLINE_EZ1");

            st.executeUpdate("INSERT INTO CRUD_ONLINE_EZ1 "
                    + "(system_name, base_date, url_message_id, adapter, screen_name, jsp_name) "
                    + "SELECT DISTINCT system_name, base_date, url_message_id, adapter, screen_name, jsp_name "
                    + "FROM stg_crud_online_ez1");

            st.executeUpdate("INSERT INTO CRUD_ONLINE_EZ2 "
                    + "(system_name, adapter, table_name, create_flag, read_flag, update_flag, delete_flag) "
                    + "SELECT system_name, adapter, table_name, "
                    + "       BOOL_OR(create_flag), BOOL_OR(read_flag), "
                    + "       BOOL_OR(update_flag), BOOL_OR(delete_flag) "
                    + "FROM stg_crud_online_ez2 "
                    + "GROUP BY system_name, adapter, table_name");
        }
    }

    private static long countRows(Connection connection, String tableName) throws SQLException {
        try (Statement st = connection.createStatement();
             ResultSet rs = st.executeQuery("SELECT COUNT(*) FROM " + tableName)) {
            rs.next();
            return rs.getLong(1);
        }
    }

    private static void rollbackQuietly(Connection connection) {
        try {
            connection.rollback();
        } catch (SQLException ignored) {
            // best effort
        }
    }

    static final class HttpClient {
        private static final int ERROR_BODY_LIMIT = 4096;
        private final Config config;
        private final CookieManager cookieManager;

        HttpClient(Config config, CookieManager cookieManager) {
            this.config = config;
            this.cookieManager = cookieManager;
        }

        void initializeSession() throws IOException {
            cookieManager.getCookieStore().removeAll();
            HttpURLConnection con = openConnection(config.baseUrl + "/ezRealCrud/ezRealCrudInit", "GET");
            try {
                int status = con.getResponseCode();
                if (status < 200 || status >= 300) {
                    throw new IOException("Session init failed. HTTP " + status
                            + ", body=" + readResponseSnippet(con, status, ERROR_BODY_LIMIT));
                }
                drainResponse(con, status);
            } finally {
                con.disconnect();
            }
        }

        SearchStats search(String adapterName, BatchInserter inserter) throws IOException, SQLException {
            IOException firstError = null;
            for (int attempt = 1; attempt <= 2; attempt++) {
                if (attempt == 2) {
                    initializeSession();
                }
                try {
                    // Stream the first page directly to PostgreSQL.  When the server reports
                    // 1000+ rows, stream the all-records response as a second pass.  The first
                    // page then exists twice in the staging tables, but publishSnapshot() uses
                    // DISTINCT / GROUP BY + BOOL_OR, so the final snapshot is unchanged while
                    // Java heap usage stays bounded.
                    SearchStats firstStats = doSearch(adapterName, false, inserter);
                    if (firstStats.resultCount >= 1000) {
                        return doSearch(adapterName, true, inserter);
                    }
                    return firstStats;
                } catch (IOException e) {
                    if (attempt == 1) {
                        firstError = e;
                        continue;
                    }
                    IOException finalError = new IOException(
                            "Search failed after retry. adapter=" + adapterName
                                    + ", firstError=" + (firstError == null ? "" : firstError.getMessage()), e);
                    throw finalError;
                }
            }
            throw new IOException("Unreachable search failure: " + adapterName);
        }

        private SearchStats doSearch(String adapterName, boolean allRecords, RowSink sink)
                throws IOException, SQLException {
            byte[] requestBody = buildFormBody(adapterName, allRecords).getBytes(StandardCharsets.UTF_8);
            HttpURLConnection con = openConnection(config.baseUrl + "/ezRealCrud/search", "POST");
            con.setDoOutput(true);
            con.setRequestProperty("Content-Type", "application/x-www-form-urlencoded; charset=UTF-8");
            con.setRequestProperty("Content-Length", String.valueOf(requestBody.length));

            try {
                try (OutputStream out = con.getOutputStream()) {
                    out.write(requestBody);
                }

                int status = con.getResponseCode();
                if (status < 200 || status >= 300) {
                    throw new IOException("HTTP " + status + " adapter=" + adapterName
                            + ", body=" + readResponseSnippet(con, status, ERROR_BODY_LIMIT));
                }

                InputStream raw = con.getInputStream();
                if (raw == null) {
                    throw new IOException("Empty HTML response adapter=" + adapterName);
                }
                Charset charset = charsetFromContentType(con.getContentType());
                SearchStats stats;
                try (InputStream in = new BufferedInputStream(raw, 16384);
                     Reader reader = new InputStreamReader(in, charset)) {
                    stats = parseSearchHtml(reader, sink);
                }

                if (!stats.validPage) {
                    throw new IOException("Unexpected search response adapter=" + adapterName
                            + ". Search page marker was not found.");
                }
                return stats;
            } finally {
                con.disconnect();
            }
        }

        private HttpURLConnection openConnection(String url, String method) throws IOException {
            HttpURLConnection con = (HttpURLConnection) new URL(url).openConnection();
            con.setRequestMethod(method);
            con.setConnectTimeout(config.connectTimeoutMs);
            con.setReadTimeout(config.readTimeoutMs);
            con.setUseCaches(false);
            con.setInstanceFollowRedirects(true);
            con.setRequestProperty("Accept", "text/html,application/xhtml+xml,*/*;q=0.8");
            con.setRequestProperty("Connection", "keep-alive");
            con.setRequestProperty("User-Agent", "CRUD-EZ-Collector/1.0");
            return con;
        }

        private String buildFormBody(String adapterName, boolean allRecords) throws IOException {
            Map<String, String> form = new LinkedHashMap<String, String>();
            form.put("transferReal", "on");
            form.put("dispCount", allRecords ? "1" : "0");
            form.put("_errorJspF", "on");
            form.put("ezRealSysnm", SYSTEM_NAME);
            form.put("ezUrl", "");
            form.put("adapter", adapterName);
            form.put("ezGamenName", "");
            form.put("ezJspName", "");
            form.put("ezTableSidPblshC", "");
            form.put("_crudJohoCF", "on");
            form.put("_crudJohoRF", "on");
            form.put("_crudJohoUF", "on");
            form.put("_crudJohoDF", "on");

            StringBuilder sb = new StringBuilder(256);
            for (Map.Entry<String, String> entry : form.entrySet()) {
                if (sb.length() > 0) {
                    sb.append('&');
                }
                sb.append(URLEncoder.encode(entry.getKey(), "UTF-8"));
                sb.append('=');
                sb.append(URLEncoder.encode(entry.getValue(), "UTF-8"));
            }
            return sb.toString();
        }

        private String readResponseSnippet(HttpURLConnection con, int status, int maxChars) throws IOException {
            InputStream raw = status >= 400 ? con.getErrorStream() : con.getInputStream();
            if (raw == null) {
                return "";
            }
            Charset charset = charsetFromContentType(con.getContentType());
            StringBuilder text = new StringBuilder(Math.min(maxChars, 1024));
            char[] buffer = new char[1024];
            try (InputStream in = new BufferedInputStream(raw, 4096);
                 Reader reader = new InputStreamReader(in, charset)) {
                int read;
                while (text.length() < maxChars && (read = reader.read(buffer)) >= 0) {
                    if (read > 0) {
                        int copy = Math.min(read, maxChars - text.length());
                        text.append(buffer, 0, copy);
                    }
                }
            }
            return abbreviate(text.toString(), 500);
        }

        private void drainResponse(HttpURLConnection con, int status) throws IOException {
            InputStream raw = status >= 400 ? con.getErrorStream() : con.getInputStream();
            if (raw == null) {
                return;
            }
            byte[] buffer = new byte[8192];
            try (InputStream in = new BufferedInputStream(raw, 8192)) {
                while (in.read(buffer) >= 0) {
                    // Consume without retaining the response in heap.
                }
            }
        }

        private Charset charsetFromContentType(String contentType) {
            if (contentType != null) {
                Matcher matcher = CHARSET_PATTERN.matcher(contentType);
                if (matcher.find()) {
                    String name = matcher.group(1);
                    try {
                        return Charset.forName(name);
                    } catch (Exception ignored) {
                        // fall through to MS932
                    }
                }
            }
            return DEFAULT_RESPONSE_CHARSET;
        }
    }

    static final class BatchInserter implements AutoCloseable, RowSink {
        private final PreparedStatement headerStatement;
        private final PreparedStatement crudStatement;
        private final int batchRows;
        private int pendingHeaders;
        private int pendingCruds;
        private boolean closed;

        BatchInserter(Connection connection, int batchRows) throws SQLException {
            this.batchRows = batchRows;
            this.headerStatement = connection.prepareStatement(
                    "INSERT INTO stg_crud_online_ez1 "
                            + "(system_name, base_date, url_message_id, adapter, screen_name, jsp_name) "
                            + "VALUES (?, ?, ?, ?, ?, ?)");
            this.crudStatement = connection.prepareStatement(
                    "INSERT INTO stg_crud_online_ez2 "
                            + "(system_name, adapter, table_name, create_flag, read_flag, update_flag, delete_flag) "
                            + "VALUES (?, ?, ?, ?, ?, ?, ?)");
        }

        @Override
        public void addHeader(HeaderRow row) throws SQLException {
            headerStatement.setString(1, SYSTEM_NAME);
            headerStatement.setString(2, nullIfEmpty(row.baseDate));
            headerStatement.setString(3, nullIfEmpty(row.urlMessageId));
            headerStatement.setString(4, nullIfEmpty(row.adapter));
            headerStatement.setString(5, nullIfEmpty(row.screenName));
            headerStatement.setString(6, nullIfEmpty(row.jspName));
            headerStatement.addBatch();
            pendingHeaders++;
            if (pendingHeaders >= batchRows) {
                flushHeaders();
            }
        }

        @Override
        public void addCrud(CrudRow row) throws SQLException {
            if (!isTargetCrudTable(row.tableName)) {
                return;
            }
            crudStatement.setString(1, SYSTEM_NAME);
            crudStatement.setString(2, nullIfEmpty(row.adapter));
            crudStatement.setString(3, nullIfEmpty(row.tableName));
            crudStatement.setBoolean(4, row.createFlag);
            crudStatement.setBoolean(5, row.readFlag);
            crudStatement.setBoolean(6, row.updateFlag);
            crudStatement.setBoolean(7, row.deleteFlag);
            crudStatement.addBatch();
            pendingCruds++;
            if (pendingCruds >= batchRows) {
                flushCruds();
            }
        }

        void flush() throws SQLException {
            flushHeaders();
            flushCruds();
        }

        private void flushHeaders() throws SQLException {
            if (pendingHeaders > 0) {
                headerStatement.executeBatch();
                headerStatement.clearBatch();
                pendingHeaders = 0;
            }
        }

        private void flushCruds() throws SQLException {
            if (pendingCruds > 0) {
                crudStatement.executeBatch();
                crudStatement.clearBatch();
                pendingCruds = 0;
            }
        }

        @Override
        public void close() throws SQLException {
            if (!closed) {
                SQLException error = null;
                try {
                    headerStatement.close();
                } catch (SQLException e) {
                    error = e;
                }
                try {
                    crudStatement.close();
                } catch (SQLException e) {
                    if (error == null) {
                        error = e;
                    } else {
                        error.addSuppressed(e);
                    }
                }
                closed = true;
                if (error != null) {
                    throw error;
                }
            }
        }

        void closeQuietly() {
            try {
                close();
            } catch (SQLException ignored) {
                // best effort
            }
        }

        private static String nullIfEmpty(String value) {
            return value == null || value.isEmpty() ? null : value;
        }
    }

    static final class Config {
        final Path baseDir;
        final String baseUrl;
        final String dbUrl;
        final String dbUser;
        final String dbPassword;
        final int connectTimeoutMs;
        final int readTimeoutMs;
        final int batchRows;
        final int commitAdapters;
        final int progressAdapters;

        Config(Path baseDir,
               String baseUrl,
               String dbUrl,
               String dbUser,
               String dbPassword,
               int connectTimeoutMs,
               int readTimeoutMs,
               int batchRows,
               int commitAdapters,
               int progressAdapters) {
            this.baseDir = baseDir;
            this.baseUrl = stripTrailingSlash(baseUrl);
            this.dbUrl = dbUrl;
            this.dbUser = dbUser;
            this.dbPassword = dbPassword;
            this.connectTimeoutMs = connectTimeoutMs;
            this.readTimeoutMs = readTimeoutMs;
            this.batchRows = batchRows;
            this.commitAdapters = commitAdapters;
            this.progressAdapters = progressAdapters;
        }

        static Config load() {
            return new Config(
                    Paths.get(property("base.dir", DEFAULT_BASE_DIR)),
                    property("base.url", DEFAULT_BASE_URL),
                    property("db.url", DEFAULT_DB_URL),
                    property("db.user", DEFAULT_DB_USER),
                    property("db.password", DEFAULT_DB_PASSWORD),
                    intProperty("connect.timeout.ms", DEFAULT_CONNECT_TIMEOUT_MS),
                    intProperty("read.timeout.ms", DEFAULT_READ_TIMEOUT_MS),
                    intProperty("batch.rows", DEFAULT_BATCH_ROWS),
                    intProperty("commit.adapters", DEFAULT_COMMIT_ADAPTERS),
                    intProperty("progress.adapters", DEFAULT_PROGRESS_ADAPTERS));
        }

        private static String property(String name, String defaultValue) {
            String value = System.getProperty(name);
            return value == null || value.trim().isEmpty() ? defaultValue : value.trim();
        }

        private static int intProperty(String name, int defaultValue) {
            String value = System.getProperty(name);
            if (value == null || value.trim().isEmpty()) {
                return defaultValue;
            }
            int parsed = Integer.parseInt(value.trim());
            if (parsed <= 0) {
                throw new IllegalArgumentException(name + " must be > 0");
            }
            return parsed;
        }

        private static String stripTrailingSlash(String value) {
            String result = value;
            while (result.endsWith("/") && result.length() > 1) {
                result = result.substring(0, result.length() - 1);
            }
            return result;
        }
    }

    static final class ScanResult {
        final Set<String> adapterNames;
        final int archiveCount;
        final int unreadableArchiveCount;

        ScanResult(Set<String> adapterNames, int archiveCount, int unreadableArchiveCount) {
            this.adapterNames = adapterNames;
            this.archiveCount = archiveCount;
            this.unreadableArchiveCount = unreadableArchiveCount;
        }
    }

    interface RowSink {
        void addHeader(HeaderRow row) throws SQLException;
        void addCrud(CrudRow row) throws SQLException;
    }

    static final class CollectingRowSink implements RowSink {
        final List<HeaderRow> headers = new ArrayList<HeaderRow>();
        final List<CrudRow> cruds = new ArrayList<CrudRow>();
        private final int maxRows;

        CollectingRowSink(int maxRows) {
            this.maxRows = maxRows;
        }

        @Override
        public void addHeader(HeaderRow row) throws SQLException {
            ensureCapacity();
            headers.add(row);
        }

        @Override
        public void addCrud(CrudRow row) throws SQLException {
            ensureCapacity();
            cruds.add(row);
        }

        private void ensureCapacity() throws SQLException {
            if ((long) headers.size() + (long) cruds.size() >= maxRows) {
                throw new SQLException("First-page buffer exceeded safety limit: " + maxRows + " rows");
            }
        }

        void flushTo(RowSink sink) throws SQLException {
            for (HeaderRow row : headers) {
                sink.addHeader(row);
            }
            for (CrudRow row : cruds) {
                sink.addCrud(row);
            }
            headers.clear();
            cruds.clear();
        }
    }

    static final class SearchStats {
        int resultCount = -1;
        long headerRows;
        long crudRows;
        boolean hasCommandMarker;
        boolean hasTitleMarker;
        boolean validPage;
        CommonValues current;
    }

    static final class CellValues {
        boolean hasAny;
        boolean hasTableName;
        String adapter;
        String baseDate;
        String url;
        String screenName;
        String jspName;
        String tableName;
        String createFlag;
        String readFlag;
        String updateFlag;
        String deleteFlag;
    }

    static final class ParsedResult {
        final List<HeaderRow> headers;
        final List<CrudRow> cruds;

        ParsedResult(List<HeaderRow> headers, List<CrudRow> cruds) {
            this.headers = headers;
            this.cruds = cruds;
        }
    }

    static final class CommonValues {
        final String systemName;
        final String baseDate;
        final String urlMessageId;
        final String adapter;
        final String screenName;
        final String jspName;

        CommonValues(String systemName,
                     String baseDate,
                     String urlMessageId,
                     String adapter,
                     String screenName,
                     String jspName) {
            this.systemName = systemName;
            this.baseDate = baseDate;
            this.urlMessageId = urlMessageId;
            this.adapter = adapter;
            this.screenName = screenName;
            this.jspName = jspName;
        }
    }

    static final class HeaderRow {
        final String systemName;
        final String baseDate;
        final String urlMessageId;
        final String adapter;
        final String screenName;
        final String jspName;

        HeaderRow(String systemName,
                  String baseDate,
                  String urlMessageId,
                  String adapter,
                  String screenName,
                  String jspName) {
            this.systemName = systemName;
            this.baseDate = baseDate;
            this.urlMessageId = urlMessageId;
            this.adapter = adapter;
            this.screenName = screenName;
            this.jspName = jspName;
        }
    }

    static final class CrudRow {
        final String systemName;
        final String adapter;
        final String tableName;
        final boolean createFlag;
        final boolean readFlag;
        final boolean updateFlag;
        final boolean deleteFlag;

        CrudRow(String systemName,
                String adapter,
                String tableName,
                boolean createFlag,
                boolean readFlag,
                boolean updateFlag,
                boolean deleteFlag) {
            this.systemName = systemName;
            this.adapter = adapter;
            this.tableName = tableName;
            this.createFlag = createFlag;
            this.readFlag = readFlag;
            this.updateFlag = updateFlag;
            this.deleteFlag = deleteFlag;
        }
    }

    private static String abbreviate(String text, int maxLength) {
        if (text == null) {
            return "";
        }
        String oneLine = text.replace('\r', ' ').replace('\n', ' ');
        return oneLine.length() <= maxLength ? oneLine : oneLine.substring(0, maxLength) + "...";
    }
}
