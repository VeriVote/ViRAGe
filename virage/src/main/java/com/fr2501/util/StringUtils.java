package com.fr2501.util;

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
}
