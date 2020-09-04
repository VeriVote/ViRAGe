package com.fr2501.util;

import java.io.IOException;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

public class ProcessUtils {
	private static final Logger logger = LogManager.getLogger(ProcessUtils.class);
	
	public static int runTerminatingProcessAndLogOutput(String command) throws IOException, InterruptedException {
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
