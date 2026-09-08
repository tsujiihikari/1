import java.io.*;
import java.nio.charset.Charset;
import java.nio.file.*;
import java.sql.*;
import java.util.*;
import java.util.regex.*;

public class Main {
    private static final String INPUT_FILE = "Input.txt";
    private static final String RESULT_FILE = "Result.txt";
    private static final int CONNECT_TIMEOUT_MS = 1000;
    private static final int LOGIN_TIMEOUT_SEC = 1;

    /*
     * 外部 Password.properties は使用しません。
     *
     * ここには「既知かつ利用許可済み」のパスワードだけを
     * DB名またはUserNameごとに1件ずつ設定してください。
     *
     * 例:
     * KNOWN_PASSWORDS.put("001_CCIS１系_EZ", "knownPassword");
     * KNOWN_PASSWORDS.put("ezowner", "knownPassword");
     */
    private static final Map<String,String> KNOWN_PASSWORDS =
            new LinkedHashMap<String,String>();

    static {
        // 明示的に把握している認証情報のみ記載
    }

    private static final Pattern KV =
            Pattern.compile("([^=;]+)=([^;]*)(?:;|$)");

    public static void main(String[] args) {
        try {
            Path input = Paths.get(INPUT_FILE);
            Path result = Paths.get(RESULT_FILE);

            if (!Files.exists(input)) {
                System.err.println("ERROR: Input.txt not found.");
                System.exit(2);
            }

            Charset cs = detectCharset(input);
            List<String> lines = Files.readAllLines(input, cs);
            List<String> out = new ArrayList<String>(lines.size());

            DriverManager.setLoginTimeout(LOGIN_TIMEOUT_SEC);

            int tested = 0;
            int success = 0;
            int skipped = 0;
            int noPassword = 0;

            for (String line : lines) {
                Entry e = parseEntry(line);

                if (e == null) {
                    out.add(line);
                    continue;
                }

                if (!"Oracle".equalsIgnoreCase(e.provider)) {
                    out.add(line);
                    skipped++;
                    System.out.println("[SKIP] " + e.name
                            + " provider=" + e.provider);
                    continue;
                }

                String password = KNOWN_PASSWORDS.get(e.name);
                if (password == null) {
                    password = KNOWN_PASSWORDS.get(e.user);
                }

                if (password == null) {
                    out.add(line);
                    noPassword++;
                    System.out.println("[NO PASSWORD] " + e.name
                            + " user=" + e.user);
                    continue;
                }

                tested++;

                if (connect(e, password)) {
                    success++;

                    out.add(line.replaceFirst(
                            "Password=[^;]*",
                            Matcher.quoteReplacement(
                                    "Password=" + password)));

                    System.out.println("[OK] " + e.name
                            + " user=" + e.user);
                } else {
                    out.add(line);

                    System.out.println("[NG] " + e.name
                            + " user=" + e.user);
                }
            }

            Files.write(result, out, cs,
                    StandardOpenOption.CREATE,
                    StandardOpenOption.TRUNCATE_EXISTING,
                    StandardOpenOption.WRITE);

            System.out.println();
            System.out.println("Completed");
            System.out.println("Tested      : " + tested);
            System.out.println("Succeeded   : " + success);
            System.out.println("No password : " + noPassword);
            System.out.println("Skipped     : " + skipped);
            System.out.println("Result      : "
                    + result.toAbsolutePath());

        } catch (Exception e) {
            e.printStackTrace();
            System.exit(1);
        }
    }

    private static boolean connect(Entry e, String password) {
        Connection connection = null;

        try {
            String url =
                    "jdbc:oracle:thin:@//"
                    + e.server + ":"
                    + e.port + "/"
                    + e.database;

            Properties props = new Properties();
            props.setProperty("user", e.user);
            props.setProperty("password", password);

            props.setProperty(
                    "oracle.net.CONNECT_TIMEOUT",
                    String.valueOf(CONNECT_TIMEOUT_MS));

            props.setProperty(
                    "oracle.jdbc.ReadTimeout",
                    String.valueOf(CONNECT_TIMEOUT_MS));

            connection =
                    DriverManager.getConnection(url, props);

            try {
                return connection.isValid(LOGIN_TIMEOUT_SEC);
            } catch (SQLFeatureNotSupportedException ex) {
                return true;
            } catch (AbstractMethodError ex) {
                return true;
            }

        } catch (SQLException ex) {
            System.out.println(
                    "  SQLState=" + ex.getSQLState()
                    + " ErrorCode=" + ex.getErrorCode()
                    + " Message=" + oneLine(ex.getMessage()));

            return false;

        } finally {
            if (connection != null) {
                try {
                    connection.close();
                } catch (SQLException ignore) {
                }
            }
        }
    }

    private static Entry parseEntry(String line) {
        if (line == null) {
            return null;
        }

        String t = line.trim();

        if (t.isEmpty()
                || t.startsWith("#")
                || t.startsWith("[")
                || !t.contains("__ConnectionType=")
                || !t.contains("ProviderName=")) {
            return null;
        }

        int eq = line.indexOf('=');
        if (eq <= 0) {
            return null;
        }

        Entry e = new Entry();
        e.name = line.substring(0, eq).trim();

        Map<String,String> values =
                new LinkedHashMap<String,String>();

        Matcher m = KV.matcher(line.substring(eq + 1));

        while (m.find()) {
            values.put(
                    m.group(1).trim(),
                    m.group(2));
        }

        e.provider = values.get("ProviderName");
        e.server = values.get("ServerName");
        e.port = values.get("Port");
        e.database = values.get("Database");
        e.user = values.get("UserName");

        if (blank(e.provider)
                || blank(e.server)
                || blank(e.port)
                || blank(e.database)
                || blank(e.user)) {
            return null;
        }

        if (e.database.startsWith("SN=")) {
            e.database =
                    e.database.substring(3);
        }

        return e;
    }

    private static Charset detectCharset(Path path)
            throws IOException {

        InputStream in = Files.newInputStream(path);

        try {
            int b1 = in.read();
            int b2 = in.read();
            int b3 = in.read();

            if (b1 == 0xEF
                    && b2 == 0xBB
                    && b3 == 0xBF) {
                return Charset.forName("UTF-8");
            }

            if (b1 == 0xFF
                    && b2 == 0xFE) {
                return Charset.forName("UTF-16LE");
            }

            if (b1 == 0xFE
                    && b2 == 0xFF) {
                return Charset.forName("UTF-16BE");
            }

        } finally {
            in.close();
        }

        return Charset.forName("MS932");
    }

    private static boolean blank(String s) {
        return s == null
                || s.trim().isEmpty();
    }

    private static String oneLine(String s) {
        if (s == null) {
            return "";
        }

        return s.replace('\r', ' ')
                .replace('\n', ' ');
    }

    private static class Entry {
        String name;
        String provider;
        String server;
        String port;
        String database;
        String user;
    }
}
