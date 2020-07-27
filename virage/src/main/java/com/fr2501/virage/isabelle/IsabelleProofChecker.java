package com.fr2501.virage.isabelle;

import java.io.IOException;
import java.io.InputStream;
import java.io.StringWriter;
import java.nio.charset.Charset;

import org.apache.commons.io.IOUtils;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

// TODO: Document
public class IsabelleProofChecker {
	private static final Logger logger = LogManager.getLogger(IsabelleProofChecker.class);
	
	private Runtime runtime;
	
	public IsabelleProofChecker() {
		this.runtime = Runtime.getRuntime();
	}
	
	public boolean verifyTheoryFile(String theory) throws IOException, InterruptedException {
		if(theory.endsWith(".thy")) {
			theory = theory.substring(0,theory.length() - ".thy".length());
		}
		
		logger.info("Starting to verify " + theory + ". This might take some time.");
		Process verificationProcess = runtime.exec("isabelle process -T" + theory);
		int status = verificationProcess.waitFor();
		
		if(status != 0) {
			// TODO: Something went wrong.
		}
		
		InputStream output = verificationProcess.getInputStream();
		StringWriter writer = new StringWriter();
		IOUtils.copy(output, writer, Charset.defaultCharset());
		
		String outputString = writer.toString();
		
		logger.debug(outputString);
		
		if(outputString.contains(IsabelleUtils.EXCEPTION)) {
			return false;
		}

		return true;
	}
}
