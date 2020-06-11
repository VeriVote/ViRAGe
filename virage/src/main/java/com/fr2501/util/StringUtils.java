package com.fr2501.util;

public class StringUtils {
	public static String removeWhitespace(String s) {
		return s.replaceAll("\\s+","");
	}
}
