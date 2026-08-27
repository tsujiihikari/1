import java.io.BufferedInputStream;
import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.InputStream;
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
    private static final Charset DEFAULT_RESPONSE_CHARSET = Charset.forName("MS932");

    private static final int DEFAULT_CONNECT_TIMEOUT_MS = 10000;
    private static final int DEFAULT_READ_TIMEOUT_MS = 60000;
    private static final int DEFAULT_BATCH_ROWS = 500;
    private static final int DEFAULT_COMMIT_ADAPTERS = 100;
    private static final int DEFAULT_PROGRESS_ADAPTERS = 100;

    private static final Pattern ROW_PATTERN = Pattern.compile(
            "(?is)<tr\\b[^>]*>(.*?)(?=<tr\\b|</tbody\\s*>|</table\\s*>|\\z)");
    private static final Pattern TARGET_CELL_PATTERN = Pattern.compile(
            "(?is)<td\\b[^>]*\\btargetId\\s*=\\s*[\"']([^\"']+)[\"'][^>]*>(.*?)</td\\s*>");
    private static final Pattern BR_PATTERN = Pattern.compile("(?is)<br\\s*/?>");
    private static final Pattern TAG_PATTERN = Pattern.compile("(?is)<[^>]+>");
    private static final Pattern WHITESPACE_PATTERN = Pattern.compile("[\\t\\r\\n ]+");
    private static final Pattern NUMERIC_ENTITY_PATTERN = Pattern.compile("&#(x?[0-9A-Fa-f]+);");
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
                        String html = http.search(adapterName);
                        ParsedResult parsed = parseSearchHtml(html);

                        for (HeaderRow row : parsed.headers) {
                            inserter.addHeader(row);
                            rowCount1++;
                        }
                        for (CrudRow row : parsed.cruds) {
                            inserter.addCrud(row);
                            rowCount2++;
                        }

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
        if (!html.contains("ezSearchRealCrudCmdInOut") || !html.contains("EZ・リアルCRUD")) {
            throw new IOException("Unexpected HTML response. Search page marker was not found.");
        }

        List<HeaderRow> headers = new ArrayList<HeaderRow>();
        List<CrudRow> cruds = new ArrayList<CrudRow>();
        CommonValues current = null;

        Matcher rowMatcher = ROW_PATTERN.matcher(html);
        while (rowMatcher.find()) {
            Map<String, String> cells = extractTargetCells(rowMatcher.group(1));
            if (cells.isEmpty()) {
                continue;
            }

            String adapter = cells.get("adapter");
            if (adapter != null && !adapter.isEmpty()) {
                current = new CommonValues(
                        valueOrEmpty(cells.get("realSysnm")),
                        valueOrEmpty(cells.get("basedate")),
                        valueOrEmpty(cells.get("url")),
                        adapter,
                        valueOrEmpty(cells.get("gamenName")),
                        valueOrEmpty(cells.get("jspName")));

                headers.add(new HeaderRow(
                        current.systemName,
                        current.baseDate,
                        current.urlMessageId,
                        current.adapter,
                        current.screenName,
                        current.jspName));
            }

            if (cells.containsKey("tableSidPblshC")) {
                if (current == null) {
                    throw new IOException("CRUD row was found before Adapter header row");
                }
                String tableName = valueOrEmpty(cells.get("tableSidPblshC"));
                if (!tableName.isEmpty() && !"-".equals(tableName)) {
                    cruds.add(new CrudRow(
                            current.systemName,
                            current.adapter,
                            tableName,
                            isCrudEnabled(cells.get("crudJohoCF")),
                            isCrudEnabled(cells.get("crudJohoRF")),
                            isCrudEnabled(cells.get("crudJohoUF")),
                            isCrudEnabled(cells.get("crudJohoDF"))));
                }
            }
        }

        return new ParsedResult(headers, cruds);
    }

    private static Map<String, String> extractTargetCells(String rowHtml) {
        Map<String, String> values = new LinkedHashMap<String, String>();
        Matcher matcher = TARGET_CELL_PATTERN.matcher(rowHtml);
        while (matcher.find()) {
            String targetId = matcher.group(1);
            String value = cleanHtmlText(matcher.group(2));
            values.put(targetId, value);
        }
        return values;
    }

    private static String cleanHtmlText(String html) {
        String text = BR_PATTERN.matcher(html).replaceAll(" ");
        text = TAG_PATTERN.matcher(text).replaceAll(" ");
        text = decodeHtmlEntities(text);
        text = text.replace('\u3000', ' ');
        text = WHITESPACE_PATTERN.matcher(text).replaceAll(" ").trim();
        return text;
    }

    private static String decodeHtmlEntities(String text) {
        String result = text
                .replace("&nbsp;", " ")
                .replace("&amp;", "&")
                .replace("&lt;", "<")
                .replace("&gt;", ">")
                .replace("&quot;", "\"")
                .replace("&#39;", "'")
                .replace("&apos;", "'");

        Matcher matcher = NUMERIC_ENTITY_PATTERN.matcher(result);
        StringBuffer sb = new StringBuffer(result.length());
        while (matcher.find()) {
            String token = matcher.group(1);
            try {
                int codePoint;
                if (token.startsWith("x") || token.startsWith("X")) {
                    codePoint = Integer.parseInt(token.substring(1), 16);
                } else {
                    codePoint = Integer.parseInt(token, 10);
                }
                matcher.appendReplacement(sb, Matcher.quoteReplacement(
                        new String(Character.toChars(codePoint))));
            } catch (RuntimeException e) {
                matcher.appendReplacement(sb, Matcher.quoteReplacement(matcher.group(0)));
            }
        }
        matcher.appendTail(sb);
        return sb.toString();
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
            st.executeUpdate("INSERT INTO CRUD_ONLINE_EZ1 "
                    + "(system_name, base_date, url_message_id, adapter, screen_name, jsp_name) "
                    + "SELECT s.system_name, s.base_date, s.url_message_id, s.adapter, s.screen_name, s.jsp_name "
                    + "FROM (SELECT DISTINCT system_name, base_date, url_message_id, adapter, screen_name, jsp_name "
                    + "      FROM stg_crud_online_ez1) s "
                    + "WHERE NOT EXISTS (SELECT 1 FROM CRUD_ONLINE_EZ1 t "
                    + "                  WHERE t.system_name = s.system_name "
                    + "                    AND t.adapter = s.adapter "
                    + "                    AND t.base_date IS NOT DISTINCT FROM s.base_date "
                    + "                    AND t.url_message_id IS NOT DISTINCT FROM s.url_message_id "
                    + "                    AND t.screen_name IS NOT DISTINCT FROM s.screen_name "
                    + "                    AND t.jsp_name IS NOT DISTINCT FROM s.jsp_name)");

            st.executeUpdate("INSERT INTO CRUD_ONLINE_EZ2 "
                    + "(system_name, adapter, table_name, create_flag, read_flag, update_flag, delete_flag) "
                    + "SELECT s.system_name, s.adapter, s.table_name, "
                    + "       s.create_flag, s.read_flag, s.update_flag, s.delete_flag "
                    + "FROM (SELECT system_name, adapter, table_name, "
                    + "             BOOL_OR(create_flag) AS create_flag, "
                    + "             BOOL_OR(read_flag) AS read_flag, "
                    + "             BOOL_OR(update_flag) AS update_flag, "
                    + "             BOOL_OR(delete_flag) AS delete_flag "
                    + "      FROM stg_crud_online_ez2 "
                    + "      GROUP BY system_name, adapter, table_name) s "
                    + "WHERE NOT EXISTS (SELECT 1 FROM CRUD_ONLINE_EZ2 t "
                    + "                  WHERE t.system_name = s.system_name "
                    + "                    AND t.adapter = s.adapter "
                    + "                    AND t.table_name = s.table_name "
                    + "                    AND t.create_flag = s.create_flag "
                    + "                    AND t.read_flag = s.read_flag "
                    + "                    AND t.update_flag = s.update_flag "
                    + "                    AND t.delete_flag = s.delete_flag)");
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
        private final Config config;
        private final CookieManager cookieManager;

        HttpClient(Config config, CookieManager cookieManager) {
            this.config = config;
            this.cookieManager = cookieManager;
        }

        void initializeSession() throws IOException {
            cookieManager.getCookieStore().removeAll();
            HttpURLConnection con = openConnection(config.baseUrl + "/ezRealCrud/ezRealCrudInit", "GET");
            int status = con.getResponseCode();
            byte[] body = readResponseBytes(con, status);
            if (status < 200 || status >= 300) {
                throw new IOException("Session init failed. HTTP " + status
                        + ", body=" + abbreviate(decodeBody(con, body), 500));
            }
        }

        String search(String adapterName) throws IOException {
            IOException firstError = null;
            for (int attempt = 1; attempt <= 2; attempt++) {
                if (attempt == 2) {
                    initializeSession();
                }
                try {
                    String html = doSearch(adapterName, false);
                    if (resultCount(html) >= 1000) {
                        html = doSearch(adapterName, true);
                    }
                    return html;
                } catch (IOException e) {
                    if (attempt == 1) {
                        firstError = e;
                        continue;
                    }
                    IOException finalError = new IOException(
                            "Search failed after retry. adapter=" + adapterName
                                    + ", firstError=" + firstError.getMessage(), e);
                    throw finalError;
                }
            }
            throw new IOException("Unreachable search failure: " + adapterName);
        }

        private String doSearch(String adapterName, boolean allRecords) throws IOException {
            byte[] requestBody = buildFormBody(adapterName, allRecords).getBytes(StandardCharsets.UTF_8);
            HttpURLConnection con = openConnection(config.baseUrl + "/ezRealCrud/search", "POST");
            con.setDoOutput(true);
            con.setRequestProperty("Content-Type", "application/x-www-form-urlencoded; charset=UTF-8");
            con.setRequestProperty("Content-Length", String.valueOf(requestBody.length));

            try (OutputStream out = con.getOutputStream()) {
                out.write(requestBody);
            }

            int status = con.getResponseCode();
            byte[] body = readResponseBytes(con, status);
            String html = decodeBody(con, body);

            if (status < 200 || status >= 300) {
                throw new IOException("HTTP " + status + " adapter=" + adapterName
                        + ", body=" + abbreviate(html, 500));
            }
            if (!html.contains("ezSearchRealCrudCmdInOut") || !html.contains("EZ・リアルCRUD")) {
                throw new IOException("Unexpected search response adapter=" + adapterName
                        + ", body=" + abbreviate(html, 500));
            }
            return html;
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

        private int resultCount(String html) {
            Matcher thMatcher = COUNT_TH_PATTERN.matcher(html);
            while (thMatcher.find()) {
                String text = cleanHtmlText(thMatcher.group(1));
                Matcher digitMatcher = DIGIT_PATTERN.matcher(text);
                if (digitMatcher.find()) {
                    String digits = digitMatcher.group(1).replace(",", "");
                    try {
                        return Integer.parseInt(digits);
                    } catch (NumberFormatException ignored) {
                        return -1;
                    }
                }
            }
            return -1;
        }

        private byte[] readResponseBytes(HttpURLConnection con, int status) throws IOException {
            InputStream raw = status >= 400 ? con.getErrorStream() : con.getInputStream();
            if (raw == null) {
                return new byte[0];
            }
            try (InputStream in = new BufferedInputStream(raw);
                 ByteArrayOutputStream out = new ByteArrayOutputStream(16384)) {
                byte[] buffer = new byte[16384];
                int read;
                while ((read = in.read(buffer)) >= 0) {
                    if (read > 0) {
                        out.write(buffer, 0, read);
                    }
                }
                return out.toByteArray();
            }
        }

        private String decodeBody(HttpURLConnection con, byte[] body) {
            Charset charset = charsetFromContentType(con.getContentType());
            return new String(body, charset);
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

    static final class BatchInserter implements AutoCloseable {
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

        void addHeader(HeaderRow row) throws SQLException {
            headerStatement.setString(1, nullIfEmpty(row.systemName));
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

        void addCrud(CrudRow row) throws SQLException {
            crudStatement.setString(1, nullIfEmpty(row.systemName));
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
