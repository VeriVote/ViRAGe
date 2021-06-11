package com.fr2501.util;

import java.io.IOException;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

/**
 * Collection of utilities for parallel process interaction and execution of
 * external programs.
 *
 */
public class ProcessUtils {
  private static final Logger logger = LogManager.getLogger(ProcessUtils.class);

  /**
   * Executes a terminating command and logs it outputs, stderr foing to
   * logger.warn(), stdout to logger.info(). <b>Does not return if the command is
   * non-terminating!</b>
   * 
   * @param command the command to be executed (as is, i.e. the String has to
   *                contain all parameters etc.)
   * @return the exit code (usually 0 on success, but depending on the command)
   * @throws IOException          if reading the outputs fails
   * @throws InterruptedException if command execution is interrupted
   */
  public static int runTerminatingProcessAndLogOutput(String command) throws IOException,
      InterruptedException {
    logger.info("Running command: " + command);

    Runtime rt = Runtime.getRuntime();

    Process p = rt.exec(command);
    int status = p.waitFor();

    String stdErr = new String(p.getErrorStream().readAllBytes());
    String stdOut = new String(p.getInputStream().readAllBytes());

    if (!stdErr.equals("")) {
      logger.warn(stdErr);
    }
    if (!stdOut.equals("")) {
      logger.info(stdOut);
    }

    return status;
  }

  /**
   * Executes a terminating command and prints its output to
   * System.out/System.err, respectively. <b>Does not return if the command is
   * non-terminating!</b>
   * 
   * @param command the command to be executed (as is, i.e. the String has to
   *                contain all parameters etc.)
   * @return the exit code (usually 0 on success, but depending on the command)
   * @throws IOException          if reading the outputs fails
   * @throws InterruptedException if command execution is interrupted
   */
  public static int runTerminatingProcessAndPrintOutput(String command) throws IOException,
      InterruptedException {
    logger.info("Running command: " + command);

    Runtime rt = Runtime.getRuntime();

    Process p = rt.exec(command);
    int status = p.waitFor();

    String stdErr = new String(p.getErrorStream().readAllBytes());
    String stdOut = new String(p.getInputStream().readAllBytes());

    if (!stdErr.equals("")) {
      System.err.print(stdErr);
    }
    if (!stdOut.equals("")) {
      System.out.print(stdOut);
    }

    return status;
  }

  public static Pair<String, String> runTerminatingProcess(String command) throws IOException, 
      InterruptedException {
    logger.info("Running command: " + command);

    Runtime rt = Runtime.getRuntime();

    Process p = rt.exec(command);
    p.waitFor();

    String stdErr = new String(p.getErrorStream().readAllBytes());
    String stdOut = new String(p.getInputStream().readAllBytes());

    return new Pair<String, String>(stdOut, stdErr);
  }
}
