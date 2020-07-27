package com.fr2501.virage.isabelle;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import com.fr2501.virage.prolog.PrologPredicate;

// TODO Document
public class IsabelleUtils {
	public static final String EXCEPTION = "Exception";
	public static final String FILE_EXTENSION = "thy";
	
	// This method tries, along with other things, to match Prolog predicates
	// to Isabelle entities. It is case-insensitive, so no two Isabelle entities
	// may share the same name with different capitalization.
	public static Map<String, Set<String>> translatePrologToIsabelle(Map<String, String> functionsAndDefinitions, String predicate) {
		Set<String> requiredFiles = new HashSet<String>();
		
		String res = predicate.replace(",", ")(");
		res = res.replace("(", " (");
		
		Pattern pattern = Pattern.compile("[a-zA-Z_]+");
		Matcher matcher = pattern.matcher(res);
	
		while(matcher.find()) {
			System.out.println(res.substring(matcher.start(), matcher.end()));
			String match = res.substring(matcher.start(), matcher.end());
			String replacement = match;
			
			for(String string: functionsAndDefinitions.keySet()) {
				if(string.equalsIgnoreCase(match)) {
					replacement = string;
					requiredFiles.add(functionsAndDefinitions.get(string));
					break;
				}
			}

			res = res.replace(match, replacement);
		}
		
		Map<String, Set<String>> resMap = new HashMap<String, Set<String>>();
		resMap.put(res, requiredFiles);
		return resMap;
	}
	
	public static Map<String, Set<String>> translatePrologToIsabelle(Map<String, String> functionsAndDefinitions, PrologPredicate predicate) {
		return translatePrologToIsabelle(functionsAndDefinitions, predicate.toString());
	}
	
	public static String getUnusedVariable(String statement) {
		String unused = "x";
		
		if(!statement.contains(unused)) return unused;
		
		for(int i=1; true; i++) {
			if(!statement.contains(unused + i)) return unused;
		}
	}
}
