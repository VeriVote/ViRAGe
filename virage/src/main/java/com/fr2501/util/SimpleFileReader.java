package com.fr2501.util;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;


public class SimpleFileReader {
	private BufferedReader reader;
	private final static Logger logger = LogManager.getLogger(SimpleFileReader.class.getName());
	
	public String readFileByLine(File file) {
		String res = "";
		
		try {
			this.reader = new BufferedReader(new FileReader(file));
		
		
			String line = reader.readLine();
			while(line != null) {
				res += line;
				line = reader.readLine();
			}
		} catch(FileNotFoundException e) {
			// TODO
			logger.error("Invalid file.");
		} catch(IOException e) {
			// TODO
			logger.error("Something went wrong while reading the file.");
		} finally {
			try {
				this.reader.close();
			} catch(IOException e) {
				// TODO
				logger.error("Reader could not be closed.");
			}
		}
		
		return res;
	}
}
