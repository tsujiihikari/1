import java.io.*;
import java.nio.charset.Charset;
import java.nio.file.*;
import java.sql.*;
import java.util.*;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

/**
 * Main.java
 *
 * Usage:
 *   java -cp ".;ojdbc8.jar" Main
 *
 * Files in current directory:
 *   Input.txt
 *   Passwords.properties
 *
 * Output:
 *   Result.txt
 *
 * Passwords.properties examples:
 *   # Prefer exact database-list name when present
 *   001_CCIS１系_EZ=actualPassword
 *
 *   # Otherwise UserName can be used as a key
 *   ezowner=actualPassword
 *   OBJECT_KYKELT=actualPassword
 *
 * Security:
 *   This program DOES NOT derive, guess, brute-force, or mutate passwords.
 *   It only tests passwords explicitly supplied in Passwords.properties.
 */
public class Main {

    private static final String INPUT_FILE = "Input.txt";
    private static final String PASSWORD_FILE = "Passwords.properties";
    private static final String RESULT_FILE = "Result.txt";

    private static final int CONNECT_TIMEOUT_MS = 1000;
    private static final int LOGIN_TIMEOUT_SEC = 1;

    private static final Pattern KV_PATTERN =
            Pattern.compile("([^=;]+)=([^;]*)(?:;|$)");

    public static void main(String[] args) {
        try {
            Path inputPath = Paths.get(INPUT_FILE);
            Path passwordPath = Paths.get(PASSWORD_FILE);
            Path resultPath = Paths.get(RESULT_FILE);

            if (!Files.exists(inputPath)) {
                System.err.println("ERROR: " + INPUT_FILE + " not found in current directory.");
                System.exit(2);
            }
            if (!Files.exists(passwordPath)) {
                System.err.println("ERROR: " + PASSWORD_FILE + " not found in current directory.");
                System.err.println("Create it with explicit authorized passwords, e.g.:");
                System.err.println("001_CCIS１系_EZ=actualPassword");
                System.err.println("ezowner=actualPassword");
                System.exit(3);
            }

            Charset charset = detectCharset(inputPath);
            List<String> lines = Files.readAllLines(inputPath, charset);
            Properties passwords = loadPropertiesPreservingUnicode(passwordPath);

            DriverManager.setLoginTimeout(LOGIN_TIMEOUT_SEC);

            List<String> output = new ArrayList<String>(lines.size());
            int tested = 0;
            int succeeded = 0;
            int skipped = 0;

            for (String line : lines) {
                if (!isDatabaseEntry(line)) {
                    output.add(line);
                    continue;
                }

                Entry entry = parseEntry(line);
                if (entry == null) {
                    output.add(line);
                    continue;
                }

                if (!"Oracle".equalsIgnoreCase(entry.providerName)) {
                    // ojdbc alone cannot connect to PostgreSQL or other providers.
                    output.add(line);
                    skipped++;
                    System.out.println("[SKIP] " + entry.name
                            + " provider=" + entry.providerName
                            + " (Oracle only; ojdbc is required)");
                    continue;
                }

                String password = lookupPassword(passwords, entry);

                if (password == null) {
                    output.add(line);
                    skipped++;
                    System.out.println("[NO PASSWORD] " + entry.name
                            + " user=" + entry.userName);
                    continue;
                }

                tested++;
                boolean ok = testOracleConnection(entry, password);

                if (ok) {
                    succeeded++;
                    output.add(replacePassword(line, password));
                    System.out.println("[OK] " + entry.name
                            + " user=" + entry.userName);
                } else {
                    output.add(line);
                    System.out.println("[NG] " + entry.name
                            + " user=" + entry.userName);
                }
            }

            Files.write(resultPath, output, charset,
                    StandardOpenOption.CREATE,
                    StandardOpenOption.TRUNCATE_EXISTING,
                    StandardOpenOption.WRITE);

            System.out.println();
            System.out.println("Completed.");
            System.out.println("Tested    : " + tested);
            System.out.println("Succeeded : " + succeeded);
            System.out.println("Skipped   : " + skipped);
            System.out.println("Output    : " + resultPath.toAbsolutePath());

        } catch (Exception e) {
            e.printStackTrace();
            System.exit(1);
        }
    }

    private static boolean isDatabaseEntry(String line) {
        if (line == null) return false;
        String t = line.trim();
        return !t.isEmpty()
                && !t.startsWith("#")
                && !t.startsWith("[")
                && t.contains("__ConnectionType=")
                && t.contains("ProviderName=");
    }

    private static Entry parseEntry(String line) {
        int firstEq = line.indexOf('=');
        if (firstEq <= 0) return null;

        String name = line.substring(0, firstEq).trim();
        String body = line.substring(firstEq + 1);

        Map<String, String> map = new LinkedHashMap<String, String>();
        Matcher m = KV_PATTERN.matcher(body);
        while (m.find()) {
            map.put(m.group(1).trim(), m.group(2));
        }

        Entry e = new Entry();
        e.name = name;
        e.providerName = map.get("ProviderName");
        e.serverName = map.get("ServerName");
        e.port = map.get("Port");
        e.database = map.get("Database");
        e.userName = map.get("UserName");

        if (isBlank(e.providerName)
                || isBlank(e.serverName)
                || isBlank(e.port)
                || isBlank(e.database)
                || isBlank(e.userName)) {
            return null;
        }

        if (e.database.startsWith("SN=")) {
            e.database = e.database.substring(3);
        }

        return e;
    }

    private static String lookupPassword(Properties passwords, Entry e) {
        // First priority: exact database-list entry name.
        String pw = passwords.getProperty(e.name);
        if (pw != null) return pw;

        // Second priority: UserName.
        pw = passwords.getProperty(e.userName);
        if (pw != null) return pw;

        return null;
    }

    private static boolean testOracleConnection(Entry e, String password) {
        Connection con = null;
        try {
            // Service-name style URL.
            String url = "jdbc:oracle:thin:@//"
                    + e.serverName + ":" + e.port + "/" + e.database;

            Properties props = new Properties();
            props.setProperty("user", e.userName);
            props.setProperty("password", password);

            // Oracle JDBC-specific millisecond timeouts.
            props.setProperty("oracle.net.CONNECT_TIMEOUT",
                    String.valueOf(CONNECT_TIMEOUT_MS));
            props.setProperty("oracle.jdbc.ReadTimeout",
                    String.valueOf(CONNECT_TIMEOUT_MS));

            con = DriverManager.getConnection(url, props);

            // Optional lightweight validity check.
            try {
                return con.isValid(LOGIN_TIMEOUT_SEC);
            } catch (AbstractMethodError ex) {
                return true;
            } catch (SQLFeatureNotSupportedException ex) {
                return true;
            }

        } catch (SQLException ex) {
            System.out.println("     SQLState=" + ex.getSQLState()
                    + " ErrorCode=" + ex.getErrorCode()
                    + " Message=" + safeMessage(ex.getMessage()));
            return false;
        } finally {
            if (con != null) {
                try {
                    con.close();
                } catch (SQLException ignore) {
                }
            }
        }
    }

    private static String replacePassword(String line, String password) {
        // Replace only the Password= value.
        // Matcher.quoteReplacement prevents $ and \ in passwords
        // from being interpreted by replaceFirst.
        return line.replaceFirst(
                "Password=[^;]*",
                Matcher.quoteReplacement("Password=" + password));
    }

    private static Properties loadPropertiesPreservingUnicode(Path path)
            throws IOException {
        Properties p = new Properties();

        Charset cs = detectCharset(path);
        BufferedReader br = Files.newBufferedReader(path, cs);
        try {
            String line;
            while ((line = br.readLine()) != null) {
                String t = line.trim();
                if (t.isEmpty() || t.startsWith("#") || t.startsWith("!")) {
                    continue;
                }

                int eq = line.indexOf('=');
                if (eq < 0) continue;

                String key = line.substring(0, eq).trim();
                String value = line.substring(eq + 1);

                p.setProperty(key, value);
            }
        } finally {
            br.close();
        }

        return p;
    }

    /**
     * Simple BOM-aware charset detection.
     * Defaults to MS932 because Japanese Windows text files often use it.
     * If your Input.txt is UTF-8 without BOM, change the default below to UTF-8.
     */
    private static Charset detectCharset(Path path) throws IOException {
        InputStream in = Files.newInputStream(path);
        try {
            int b1 = in.read();
            int b2 = in.read();
            int b3 = in.read();

            if (b1 == 0xEF && b2 == 0xBB && b3 == 0xBF) {
                return Charset.forName("UTF-8");
            }
            if (b1 == 0xFF && b2 == 0xFE) {
                return Charset.forName("UTF-16LE");
            }
            if (b1 == 0xFE && b2 == 0xFF) {
                return Charset.forName("UTF-16BE");
            }
        } finally {
            in.close();
        }

        return Charset.forName("MS932");
    }

    private static boolean isBlank(String s) {
        return s == null || s.trim().isEmpty();
    }

    private static String safeMessage(String s) {
        if (s == null) return "";
        return s.replace('\r', ' ').replace('\n', ' ');
    }

    private static class Entry {
        String name;
        String providerName;
        String serverName;
        String port;
        String database;
        String userName;
    }
}
