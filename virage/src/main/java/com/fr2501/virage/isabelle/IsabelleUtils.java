package com.fr2501.virage.isabelle;

import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

public class IsabelleUtils {
	// This method tries, along with other things, to match Prolog predicates
	// to Isabelle entities. It is case-insensitive, so no two Isabelle entities
	// may share the same name with different capitalization.
	public static String translatePrologToIsabelle(Set<String> functionsAndDefinitions, String prologString) {
		String res = prologString.replace(",", ")(");
		res = res.replace("(", " (");
		
		Pattern pattern = Pattern.compile("[a-zA-Z_]+");
		Matcher matcher = pattern.matcher(res);
	
		while(matcher.find()) {
			System.out.println(res.substring(matcher.start(), matcher.end()));
			String match = res.substring(matcher.start(), matcher.end());
			String replacement = match;
			
			for(String string: functionsAndDefinitions) {
				if(string.equalsIgnoreCase(match)) {
					replacement = string;
					break;
				}
			}

			res = res.replace(match, replacement);
		}
		
		//TODO: Drop and Pass module require a second parameter.
		
		return res;
	}
}
