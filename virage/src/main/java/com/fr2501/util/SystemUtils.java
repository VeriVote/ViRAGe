package com.fr2501.util;

import java.io.File;
import java.io.IOException;
import java.lang.reflect.Field;
import java.time.LocalDateTime;
import java.time.format.DateTimeFormatter;
import java.util.Map;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

/**
 * A set of system utility functions.
 *
 * @author VeriVote
 */
public class SystemUtils {
    /**
     * The logger.
     */
    private static final Logger LOGGER = LogManager.getRootLogger();

    /**
     * The java.library.path system property.
     */
    private static final String JAVA_LIBRARY_PATH = "java.library.path";

    // See
    // https://stackoverflow.com/questions/5419039/
    // is-djava-library-path-equivalent-to-system-setpropertyjava-library-path
    /**
     * A method to add paths to LD_LIBRARY_PATH. If possible, do not use this.
     *
     * @param s the path to be added
     * @throws IOException if adding s to LD_LIBRARY_PATH is not possible
     */
    public static void addDirToLibraryPath(final String s) throws IOException {
        try {
            // This enables the java.library.path to be modified at runtime
            // From a Sun engineer at http://forums.sun.com/thread.jspa?threadID=707176
            //
            final Field field = ClassLoader.class.getDeclaredField("usr_paths");
            field.setAccessible(true);
            final String[] paths = (String[]) field.get(null);
            for (int i = 0; i < paths.length; i++) {
                if (s.equals(paths[i])) {
                    return;
                }
            }
            final String[] tmp = new String[paths.length + 1];
            System.arraycopy(paths, 0, tmp, 0, paths.length);
            tmp[paths.length] = s;
            field.set(null, tmp);
            System.setProperty(JAVA_LIBRARY_PATH,
                    System.getProperty(JAVA_LIBRARY_PATH) + File.pathSeparator + s);
        } catch (final IllegalAccessException e) {
            throw new IOException("Failed to get permissions to set library path");
        } catch (final NoSuchFieldException e) {
            throw new IOException("Failed to get field handle to set library path");
        }
    }

    /**
     * Returns current time (yyyy-MM-dd HH:mm:ss).
     * @return the time
     */
    public static String getTime() {
        final DateTimeFormatter dtf = DateTimeFormatter.ofPattern("yyyy-MM-dd HH:mm:ss");
        final LocalDateTime now = LocalDateTime.now();

        return dtf.format(now);
    }

    // TODO This is terrible and I know it. "export" is not possible from Java?
    /**
     * A method to set environment variables on Unix systems.
     *
     * @param name the environment variable to be changed
     * @param value the new value of said variable
     */
    @SuppressWarnings("unchecked")
    public static void setUnixEnvironmentVariable(final String name, final String value) {
        final Map<String, String> env = System.getenv();

        final Field field;
        try {
            field = env.getClass().getDeclaredField("m");

            field.setAccessible(true);
            ((Map<String, String>) field.get(env)).put(name, value);
        } catch (final NoSuchFieldException e) {
            e.printStackTrace();
        } catch (final SecurityException e) {
            e.printStackTrace();
        } catch (final IllegalArgumentException e) {
            e.printStackTrace();
        } catch (final IllegalAccessException e) {
            e.printStackTrace();
        }

        LOGGER.info("New value: " + System.getenv(name));
        if (!System.getenv(name).equals(value)) {
            LOGGER.error("Setting environment variable " + name + " to " + value + " failed.");
        }
    }

    /**
     * Helper method to let a thread sleep for 100ms without worrying about exceptions.
     */
    public static void semiBusyWaitingHelper() {
        final int defaultWait = 100;

        semiBusyWaitingHelper(defaultWait);
    }

    /**
     * Helper method to let a thread sleep without worrying about exceptions.
     * @param timeout the sleep duration
     */
    public static void semiBusyWaitingHelper(final long timeout) {
        try {
            Thread.sleep(timeout);
        } catch (final InterruptedException e) {
            // No-op
        }
    }
}
