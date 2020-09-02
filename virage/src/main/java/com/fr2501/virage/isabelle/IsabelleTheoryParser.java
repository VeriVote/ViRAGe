package com.fr2501.virage.isabelle;

import java.io.File;
import java.io.IOException;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import com.fr2501.util.SimpleFileReader;
import com.fr2501.util.StringUtils;

/**
 * 
 * Very simple parser for Isabelle theories, nowhere near complete.
 *
 */
public class IsabelleTheoryParser {
	private static final String DEFINITION = "definition";
	private static final String FUNCTION = "fun";
	private static final String EQUIV = "\\<equiv>";
	
	/**
	 * Extracts all functions and definitions from a folder or a single file 
	 * of Isabelle theories and maps them to the file they originate from.
	 * @param path the path
	 * @return a map containing all functions and definitions and their corresponding files
	 * @throws IOException if file system interaction fails
	 */
	public Map<String, String> getAllFunctionsAndDefinitions(String path) throws IOException {
		Map<String, String> res = new HashMap<String, String>();
		
		File pathFile = new File(path).getCanonicalFile();
		
		File[] files;
		if(pathFile.isDirectory()) {
			files = pathFile.listFiles();
		} else {
			files = new File[1];
			files[0] = pathFile;
		}
		
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
	
	/**
	 * This method returns a list of all imports in the given theory file
	 * @param theory the .thy-file
	 * @return a list of the imports
	 * @throws IOException if reading the file is not possible
	 */
	public List<String> getImportsFromTheoryFile(File theory) throws IOException {
		List<String> res = new LinkedList<String>();
		SimpleFileReader reader = new SimpleFileReader();
		
		List<String> lines = reader.readFileByLine(theory);
		
		for(String line: lines) {
			if(line.contains(IsabelleUtils.IMPORTS)) {
				String[] splits = line.split(" ");
				
				for(String split: splits) {
					if(StringUtils.removeWhitespace(split).equals("")
							|| split.equals(IsabelleUtils.IMPORTS)) {
						continue;
					}
					
					res.add(split);
				}
				
				return res;
			}
		}
		
		// No imports found.
		return res;
	}
	
	// TODO: Document
	public String getDefinitionByName(String name, File theory) throws IOException {
		SimpleFileReader reader = new SimpleFileReader();
		
		String prefix = DEFINITION + name;
		
		List<String> lines = reader.readFileByLine(theory);
		
		for(int i=0; i<lines.size(); i++) {
			String line = lines.get(i);
			
			if(StringUtils.removeWhitespace(line).startsWith(prefix)) {
				return line + "\n" + lines.get(i+1);
			}
		}
		
		throw new IllegalArgumentException();
	}
}
