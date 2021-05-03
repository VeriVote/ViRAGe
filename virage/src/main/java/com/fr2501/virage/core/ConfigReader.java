package com.fr2501.virage.core;

import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.util.Collections;
import java.util.LinkedList;
import java.util.List;
import java.util.Properties;

import com.fr2501.util.Pair;

public class ConfigReader {
	private static final String LIST_SEPARATOR = ";";
	
	private Properties properties;
	
	public ConfigReader() {
		try {
			this.readConfigFile();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}
	
	public void readConfigFile() throws IOException {
		this.properties = new Properties();
		
		FileInputStream input = new FileInputStream(this.getClass().getClassLoader().getResource("config.properties").getFile());
		
		this.properties.load(input);
	}
	
	public List<String> getIsabelleTactics() {
		return this.readAndSplitList("isabelle_tactics");
	}
	
	public List<Pair<String,String>> getTypeSynonyms() {
		List<Pair<String,String>> res = new LinkedList<Pair<String,String>>();
		List<String> typeSynonyms = this.readAndSplitList("type_synonyms");
		
		for(String synonym: typeSynonyms) {
			String[] splits = synonym.split("->");
			
			if(splits.length != 2) throw new IllegalArgumentException();
			
			res.add(new Pair<String,String>(splits[0], splits[1]));
		}
		
		return res;
	}
	
	public List<String> getAtomicTypes() {
		return this.readAndSplitList("atomic_types");
	}
	
	private List<String> readAndSplitList(String key) {
		String list = (String) this.properties.get(key);
		String[] splits = list.split(LIST_SEPARATOR);
		
		List<String> result = new LinkedList<String>();
		for(int i=0; i<splits.length; i++) {
			result.add(splits[i]);
		}
		
		return result;
	}
	
	public List<String> getAdditionalProperties() {
		return this.readAndSplitList("additional_properties");
	}
	
}
