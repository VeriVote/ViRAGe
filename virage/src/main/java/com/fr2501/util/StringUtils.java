package com.fr2501.util;

import java.util.Collection;

/**
 * 
 * A collection of useful String utilities
 *
 */
public class StringUtils {
	
	/**
	 * Removes whitespace from String
	 * 
	 * @param s the String
	 * @return new String, s without whitespace
	 */
	public static String removeWhitespace(String s) {
		return s.replaceAll("\\s+","");
	}
	
	/**
	 * Creates a comma-separated String from a collection.
	 * @param c the collection
	 * @return the String, empty if c is empty
	 */
	public static String printCollection(Collection<?> c) {
		if(c.isEmpty()) return "";
		
		String res = "";
		
		for(Object obj: c) {
			res += obj.toString() + ",";
		}
		
		res = res.substring(0, res.length()-1);
		
		return res;
	}
}
