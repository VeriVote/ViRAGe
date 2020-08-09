package com.fr2501.virage.isabelle;

import java.io.File;
import java.io.IOException;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import com.fr2501.util.SimpleFileReader;

/**
 * 
 * Very simple parser for Isabelle theories, nowhere near complete.
 *
 */
public class IsabelleTheoryParser {
	private static final String DEFINITION = "definition";
	private static final String FUNCTION = "fun";
	
	/**
	 * Extracts all functions and definitions from a folder of Isabelle theories and
	 * maps them to the file they originate from.
	 * @param path the path
	 * @return a map containing all functions and definitions and their corresponding files
	 * @throws IOException if file system interaction fails
	 */
	public Map<String, String> getAllFunctionsAndDefinitions(String path) throws IOException {
		Map<String, String> res = new HashMap<String, String>();
		
		File folder = new File(path).getCanonicalFile();
		
		if(!folder.isDirectory()) {
			throw new IllegalArgumentException();
		}
		
		File[] files = folder.listFiles();
		
		SimpleFileReader reader = new SimpleFileReader();
		for(File file: files) {
			if(!file.getAbsolutePath().endsWith(IsabelleUtils.FILE_EXTENSION)) {
				continue;
			}
			
			List<String> lines = reader.readFileByLine(file);
			
			for(String line: lines) {
				if(line.startsWith(DEFINITION) || line.startsWith(FUNCTION)) {
					String[] splits = line.split(" ");
					// Name of the object is second "word" on the line.
					res.put(splits[1], file.getName());
				}
			}
		}
		
		return res;
	}
}
