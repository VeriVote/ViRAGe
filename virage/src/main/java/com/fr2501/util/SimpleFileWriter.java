package com.fr2501.util;

import java.io.BufferedReader;
import java.io.FileWriter;
import java.io.IOException;
import java.util.Collection;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

/**
 * 
 * Utility class to write files line by line.
 *
 */
public class SimpleFileWriter {
	private FileWriter writer;
	private final static Logger logger = LogManager.getLogger(SimpleFileWriter.class.getName());
	
	/**
	 * Writes Collection to file, with every item on its own line, creates file if needed.
	 * @param path the file to be written to
	 * @param collection the collection
	 */
	public void writeCollectionToFile(String path, Collection<?> collection) {
		try {
			this.writer = new FileWriter(path);
			
			for(Object o: collection) {
				writer.write(o.toString() + "\n");
			}
		} catch (IOException e) {
			logger.warn("Writing to " + path + " was impossible.");
		} finally {
			try {
				this.writer.close();
			} catch (IOException e) {
				logger.warn("Closing the FileWriter was impossible.");
			}
		}
	}
}
