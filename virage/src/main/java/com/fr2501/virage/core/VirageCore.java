package com.fr2501.virage.core;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

/**
 * Hello world!
 *
 */
public class VirageCore 
{
	private final static String _NAME = "ViRAGe";
	private final static String _VERSION = "0.0.1";
	private final static Logger logger = LogManager.getLogger(VirageCore.class.getName());
	
    public static void main(String[] args) {
        logger.info("--- " + _NAME + " version " + _VERSION);
    }
}
