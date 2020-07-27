package com.fr2501.virage.isabelle;

import java.io.File;
import java.io.IOException;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import com.fr2501.util.SimpleFileReader;

// TODO: Document
public class IsabelleTheoryParser {
	private static final String DEFINITION = "definition";
	private static final String FUNCTION = "fun";
	private static final String ISABELLE_EXTENSION = ".thy";
	
	public Map<String, String> getAllFunctionsAndDefinitions(String path) throws IOException {
		Map<String, String> res = new HashMap<String, String>();
		
		File folder = new File(path);
		
		if(!folder.isDirectory()) {
			throw new IllegalArgumentException();
		}
		
		File[] files = folder.listFiles();
		
		SimpleFileReader reader = new SimpleFileReader();
		for(File file: files) {
			if(!file.getAbsolutePath().endsWith(ISABELLE_EXTENSION)) {
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
