package com.fr2501.virage.core;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

/**
 * 
 * The main entry point
 *
 */
public class VirageMain {
	private final static Logger logger = LogManager.getLogger(VirageMain.class);
	
	private final static String _NAME = "ViRAGe";
	private final static String _VERSION = "0.0.1";
	
	public static void main(String[] args) {
		logger.info("--- " + _NAME + " version " + _VERSION);
		
		try {
			VirageCore core = new VirageCore(args);
			Thread coreThread = new Thread(core, "core");
			coreThread.start();
		} catch (Exception e) {
			logger.fatal("An unrecoverable error has occured.", e);
			logger.fatal("The program will now terminate.");
		}
		
        logger.info("--- Terminating " + _NAME + ".");
		return;
	}
}
