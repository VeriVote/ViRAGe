package edu.kit.kastel.formal.util;

import java.io.File;
import java.io.IOException;
import java.nio.charset.StandardCharsets;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

/**
 * Collection of utilities for parallel process interaction and execution of external programs.
 *
 * @author VeriVote
 */
public final class ProcessUtils {
    /**
     * The logger.
     */
    private static final Logger LOGGER = LogManager.getLogger(ProcessUtils.class);

    private ProcessUtils() { }

    /**
     * Start process for given editorExecutable in given file path.
     *
     * @param editorExecutable executable editor
     * @param path the given file path
     */
    public static void start(final String editorExecutable, final File path) {
        final ProcessBuilder pb =
                new ProcessBuilder(StringUtils.stripAndEscape(editorExecutable),
                                   path.getAbsolutePath());
        try {
            final Process process = pb.directory(null).start();
            process.waitFor();
        } catch (final InterruptedException e) {
            e.printStackTrace();
        } catch (final IOException e) {
            e.printStackTrace();
        }
    }

    /**
     * Executes a terminating command and prints its output to System.out/System.err, respectively.
     * <b>Does not return if the command is non-terminating!</b>
     *
     * @param command the command to be executed (as is, i.e. the String has to contain all
     *      parameters etc.)
     * @return a Pair of strings representing standard output and standard error of the process
     * @throws IOException if reading the outputs fails
     * @throws InterruptedException if command execution is interrupted
     */
    public static Output runTerminatingProcess(final String command)
            throws IOException, InterruptedException {
        final Runtime rt = Runtime.getRuntime();
        final Process p = rt.exec(StringUtils.stripAndEscape(command));
        final int status = p.waitFor();
        final String stdErr = new String(p.getErrorStream().readAllBytes(), StandardCharsets.UTF_8);
        final String stdOut = new String(p.getInputStream().readAllBytes(), StandardCharsets.UTF_8);
        return new Output(stdOut, stdErr, status);
    }

    /**
     * Executes a terminating command and logs it outputs, standard error going to logger.warn(),
     * standard output to logger.info(). <b>Does not return if the command is non-terminating!</b>
     *
     * @param command the command to be executed (as is, i.e. the String has to contain all
     *      parameters etc.)
     * @return the exit code (usually 0 on success, but depending on the command)
     * @throws IOException if reading the outputs fails
     * @throws InterruptedException if command execution is interrupted
     */
    public static int runTerminatingProcessAndLogOutput(final String command)
            throws IOException, InterruptedException {
        final Output output = runTerminatingProcess(command);
        if (!output.stdErr.isEmpty()) {
            LOGGER.warn(output.stdErr);
        }
        if (!output.stdOut.isEmpty()) {
            LOGGER.info(output.stdOut);
        }
        return output.status;
    }

    /**
     * Executes a terminating command and prints its output to System.out/System.err, respectively.
     * <b>Does not return if the command is non-terminating!</b>
     *
     * @param command the command to be executed (as is, i.e. the String has to contain all
     *      parameters etc.)
     * @return the exit code (usually 0 on success, but depending on the command)
     * @throws IOException if reading the outputs fails
     * @throws InterruptedException if command execution is interrupted
     */
    public static int runTerminatingProcessAndPrintOutput(final String command)
            throws IOException, InterruptedException {
        final Output output = runTerminatingProcess(command);
        if (!output.stdErr.isEmpty()) {
            System.err.print(output.stdErr);
        }
        if (!output.stdOut.isEmpty()) {
            System.out.print(output.stdOut);
        }
        return output.status;
    }

    /**
     * The static data structure to store the text from the standard output and the error output
     * stream as well as the integer status value.
     *
     * @author VeriVote
     */
    public static class Output {
        /**
         * The standard output stream as a string.
         */
        public final String stdOut;

        /**
         * The error output stream as a string.
         */
        public final String stdErr;

        /**
         * The status output as an integer value.
         */
        public final int status;

        /**
         * Constructor method for the static data structure to store the text from the standard
         * output and the error output stream as well as the integer status value.
         *
         * @param outStream The standard output stream as a string.
         * @param errStream The error output stream as a string.
         * @param statusValue The status output as an integer value.
         */
        public Output(final String outStream, final String errStream, final int statusValue) {
            stdOut = outStream;
            stdErr = errStream;
            status = statusValue;
        }
    }
}
