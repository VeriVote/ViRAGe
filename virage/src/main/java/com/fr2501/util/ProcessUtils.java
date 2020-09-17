package com.fr2501.util;

import java.io.IOException;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

public class ProcessUtils {
	private static final Logger logger = LogManager.getLogger(ProcessUtils.class);
	
	/**
	 * Executes a terminating command and logs it outputs, stderr foing to logger.warn(), stdout to logger.info().
	 * <b>Does not return if the command is non-terminating!</b>
	 * @param command the command to be executed (as is, i.e. the String has to contain all parameters etc.)
	 * @return the exit code (usually 0 on success, but depending on the command)
	 * @throws IOException if reading the outputs fails
	 * @throws InterruptedException if command execution is interrupted
	 */
	public static int runTerminatingProcessAndLogOutput(String command) throws IOException, InterruptedException {
		logger.info("Running command: " + command);
		
		Runtime rt = Runtime.getRuntime();
		
		Process p = rt.exec(command);
		int status = p.waitFor();
		
		String stdErr = new String(p.getErrorStream().readAllBytes());
		String stdOut = new String(p.getInputStream().readAllBytes());
		
		if(!stdErr.equals("")) logger.warn(stdErr);
		if(!stdOut.equals("")) logger.info(stdOut);
		
		return status;
	}
}
