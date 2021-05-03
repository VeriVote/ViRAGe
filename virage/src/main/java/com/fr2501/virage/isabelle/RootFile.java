package com.fr2501.virage.isabelle;

import java.io.File;
import java.io.IOException;
import java.util.List;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import org.checkerframework.common.returnsreceiver.qual.This;

import com.fr2501.util.SimpleFileReader;

/**
 * 
 * TODO
 *
 */
public class RootFile {
	private static Logger logger = LogManager.getRootLogger();
	
	private File file;
	
	private List<String> lines;
	private String sessionName;
	private List<String> theoryNames;
	
	public RootFile(File file) {
		this.file = file;
		
		SimpleFileReader reader = new SimpleFileReader();
		
		try {
			this.lines = reader.readFileByLine(file);
		} catch (IOException e) {
			logger.warn(e);
		}
	}
	
	private void parseFile() {
		for(int i=0; i<this.lines.size(); i++) {
			String line = lines.get(i);
			
			// TODO
		}
	}
}
