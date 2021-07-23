package com.fr2501.util;

import java.io.IOException;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

/**
 * Collection of utilities for parallel process interaction and execution of external programs.
 *
 * @author VeriVote
 */
public class ProcessUtils {
    /**
     * The logger.
     */
    private static final Logger LOGGER = LogManager.getLogger(ProcessUtils.class);

    /**
     * Executes a terminating command and logs it outputs, stderr foing to logger.warn(), stdout to
     * logger.info(). <b>Does not return if the command is non-terminating!</b>
     *
     * @param command the command to be executed (as is, i.e. the String has to contain all
     *      parameters etc.)
     * @return the exit code (usually 0 on success, but depending on the command)
     * @throws IOException if reading the outputs fails
     * @throws InterruptedException if command execution is interrupted
     */
    public static int runTerminatingProcessAndLogOutput(final String command)
            throws IOException, InterruptedException {
        LOGGER.info("Running command: " + command);

        final Runtime rt = Runtime.getRuntime();

        final Process p = rt.exec(command);
        final int status = p.waitFor();

        final String stdErr = new String(p.getErrorStream().readAllBytes());
        final String stdOut = new String(p.getInputStream().readAllBytes());

        if (!stdErr.isEmpty()) {
            LOGGER.warn(stdErr);
        }
        if (!stdOut.isEmpty()) {
            LOGGER.info(stdOut);
        }

        return status;
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
        LOGGER.info("Running command: " + command);

        final Runtime rt = Runtime.getRuntime();

        final Process p = rt.exec(command);
        final int status = p.waitFor();

        final String stdErr = new String(p.getErrorStream().readAllBytes());
        final String stdOut = new String(p.getInputStream().readAllBytes());

        if (!stdErr.isEmpty()) {
            System.err.print(stdErr);
        }
        if (!stdOut.isEmpty()) {
            System.out.print(stdOut);
        }

        return status;
    }

    /**
     * Executes a terminating command and prints its output to System.out/System.err, respectively.
     * <b>Does not return if the command is non-terminating!</b>
     *
     * @param command the command to be executed (as is, i.e. the String has to contain all
     *      parameters etc.)
     * @return a Pair of strings representing stdout and stderr of the process
     * @throws IOException if reading the outputs fails
     * @throws InterruptedException if command execution is interrupted
     */
    public static Pair<String, String> runTerminatingProcess(final String command)
            throws IOException, InterruptedException {
        LOGGER.info("Running command: " + command);

        final Runtime rt = Runtime.getRuntime();

        final Process p = rt.exec(command);
        p.waitFor();

        final String stdErr = new String(p.getErrorStream().readAllBytes());
        final String stdOut = new String(p.getInputStream().readAllBytes());

        return new Pair<String, String>(stdOut, stdErr);
    }
}
