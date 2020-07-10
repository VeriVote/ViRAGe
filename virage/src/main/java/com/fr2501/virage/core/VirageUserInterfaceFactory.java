package com.fr2501.virage.core;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

// TODO Document
public class VirageUserInterfaceFactory {
	private static final Logger logger = LogManager.getLogger(VirageUserInterfaceFactory.class);
	
	public VirageUserInterface getUI(String string, VirageCore core) {
		VirageUserInterface res;
		
		if(string.equals(VirageStrings.CLI_ARG)) {
			res = new VirageCommandLineInterface(core);
			
		} else {
			logger.info("Invalid ui value, defaulting to cli.");
			res = new VirageCommandLineInterface(core);
		}
		
		return res;
	}
}
