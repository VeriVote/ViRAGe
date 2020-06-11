package com.fr2501.util;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.util.LinkedList;
import java.util.List;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

/**
 * 
 * Utility class to read files line by line.
 *
 */
public class SimpleFileReader {
	private BufferedReader reader;
	private final static Logger logger = LogManager.getLogger(SimpleFileReader.class.getName());
	
	/**
	 * Reads the specified file line by line.
	 * 
	 * @param file the file to be read.
	 * @return a list containing the lines of that file.
	 * @throws IOException if reading the file is not possible.
	 */
	public List<String> readFileByLine(File file) throws IOException {
		logger.info("Trying to read from file \"" + file + "\"");
		
		List<String> res = new LinkedList<String>();
		
		try {
			this.reader = new BufferedReader(new FileReader(file));
		
		
			String line = reader.readLine();
			while(line != null) {
				res.add(line);
				line = reader.readLine();
			}
		} catch(FileNotFoundException e) {
			logger.fatal("Invalid file.");
			throw e;
		} catch(IOException e) {
			logger.fatal("Something went wrong while reading the file.");
			throw e;
		}
		
		return res;
	}
}
