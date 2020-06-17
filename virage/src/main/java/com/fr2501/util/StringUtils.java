package com.fr2501.util;

import java.util.Collection;
import java.util.regex.Pattern;

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
	
	/**
	 * Checks whether a String is a number
	 * @param strNum 
	 * @return true if strNum represents a number, false otherwise.
	 */
	public static boolean isNumeric(String strNum) {
		Pattern pattern = Pattern.compile("-?\\d+(\\.\\d+)?");
		
	    if (strNum == null) {
	        return false; 
	    }
	    return pattern.matcher(strNum).matches();
	}
}
