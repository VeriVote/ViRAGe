package edu.kit.kastel.formal.util;

import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.io.StringWriter;
import java.lang.reflect.Field;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.time.Duration;
import java.time.Instant;
import java.time.ZoneId;
import java.time.format.DateTimeFormatter;

import org.apache.commons.io.FilenameUtils;
import org.apache.commons.io.IOUtils;
import org.apache.commons.lang3.time.DurationFormatUtils;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

/**
 * A set of system utility functions.
 *
 * @author VeriVote
 */
public final class SystemUtils {
    /**
     * Resources directory.
     */
    public static final String RESOURCES = "src/test/resources/";

    /**
     * The logger.
     */
    private static final Logger LOGGER = LogManager.getRootLogger();

    /**
     * The java.library.path system property.
     */
    private static final String JAVA_LIBRARY_PATH = "java.library.path";

    /**
     * The user paths field.
     */
    private static final String USER_PATHS_FIELD = "usr_paths";

    /**
     * The pattern for printing time markers.
     */
    private static final String TIMESTAMP_PATTERN = "yyyy-MM-dd HH:mm:ss OOOO";

    /**
     * String with the library failure reason due to insufficient permissions.
     */
    private static final String PERMISSIONS_EXC_REASON = "permissions";

    /**
     * String with the library failure reason due to insufficient field handle.
     */
    private static final String FIELD_HANDLE_EXC_REASON = "field handle";

    private SystemUtils() { }

    private static String libraryFailureReason(final String reasonForFailure) {
        return "Failed to get " + reasonForFailure + " to set library path";
    }

    /**
     * Sanitize a raw file name and create file.
     *
     * @param rawFileName the raw file name as a string value
     * @return the new file with a sanitized file name
     * @throws IOException in case the file is invalid
     */
    private static File createSanitizedFile(final String rawFileName) throws IOException {
        return new File(FilenameUtils.getFullPath(rawFileName),
                        FilenameUtils.getName(rawFileName)).getCanonicalFile();
    }

    /**
     * Sanitize a raw file name, drop its path and create file.
     *
     * @param rawFileName the raw file name as a string value
     * @return the new file with a sanitized file name
     * @throws IOException in case the file is invalid
     */
    private static File createSanitizedFileWithoutPath(final String rawFileName) {
        return new File(FilenameUtils.getName(rawFileName));
    }

    /**
     * Sanitize a raw file name and create file, in case of problems drop the path.
     *
     * @param rawFileName the raw file name as a string value
     * @return the new file with a sanitized file name
     */
    public static File file(final String rawFileName) {
        File file;
        try {
            file = createSanitizedFile(rawFileName);
        } catch (IOException e) {
            file = createSanitizedFileWithoutPath(rawFileName);
            e.printStackTrace();
        }
        return file;
    }

    /**
     * Sanitize a raw file name and create temporary file.
     *
     * @param rawFileName the raw file name as a string value
     * @param fileExtension the file extension
     * @return the new temporary file with a sanitized file name
     * @throws IOException in case creating the temporary file fails
     */
    public static File tempFile(final String rawFileName, final String fileExtension)
            throws IOException {
        return File.createTempFile(FilenameUtils.getName(rawFileName), fileExtension);
    }

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
            final Field field = ClassLoader.class.getDeclaredField(USER_PATHS_FIELD);
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
            throw new IOException(libraryFailureReason(PERMISSIONS_EXC_REASON));
        } catch (final NoSuchFieldException e) {
            throw new IOException(libraryFailureReason(FIELD_HANDLE_EXC_REASON));
        }
    }

    /**
     * Returns formatted time.
     *
     * @param time the time that should be formatted
     * @return the time
     */
    public static String getTime(final long time) {
        return DateTimeFormatter.ofPattern(TIMESTAMP_PATTERN)
                .format(Instant.ofEpochMilli(time).atZone(ZoneId.systemDefault()));
    }

    /**
     * Returns current time for usage as time markers.
     *
     * @return the time
     */
    public static String getCurrentTime() {
        return getTime(System.currentTimeMillis());
    }

    /**
     * Returns elapsed duration between start and end time.
     *
     * @param start start time
     * @param end end time
     * @return the duration in some readable string format
     */
    public static String getDuration(final long start, final long end) {
        final Duration endTime = Duration.ofMillis(end);
        final Duration startTime = Duration.ofMillis(start);
        return DurationFormatUtils.formatDurationHMS(endTime.minus(startTime).toMillis());
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
     *
     * @param timeout the sleep duration
     */
    public static void semiBusyWaitingHelper(final long timeout) {
        try {
            Thread.sleep(timeout);
        } catch (final InterruptedException e) {
            // Skip operation
        }
    }

    /**
     * Terminates ViRAGe.
     *
     * @param statusCode ViRAGe's exit code
     */
    public static synchronized void exit(final int statusCode) {
        System.exit(statusCode);
    }

    /**
     * Copies a resource to the file system.
     *
     * @param resource the resource
     * @param path the path of the file to be created
     */
    public static void copyResourceToFile(final String resource, final String path) {
        final File newFile = file(path);
        try {
            Files.deleteIfExists(newFile.toPath());
        } catch (final IOException e1) {
            e1.printStackTrace();
        }
        String content = StringUtils.EMPTY;
        final InputStream theoryTemplateStream = SystemUtils.class.getClassLoader()
                .getResourceAsStream(resource);
        final StringWriter writer = new StringWriter();
        try {
            IOUtils.copy(theoryTemplateStream, writer, StandardCharsets.UTF_8);
        } catch (final IOException e) {
            LOGGER.error(e);
        }
        content = writer.toString();
        final SimpleFileWriter fileWriter = new SimpleFileWriter();
        fileWriter.writeToFile(path, content);
    }
}
