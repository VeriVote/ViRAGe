package com.fr2501.util;

import java.util.Collection;
import java.util.LinkedList;
import java.util.List;
import java.util.regex.Pattern;

/**
 * A collection of useful String utilities.
 *
 * @author VeriVote
 */
public class StringUtils {

    /**
     * Checks whether a String is a number.
     *
     * @param strNum the String to be checked
     * @return true if strNum represents a number, false otherwise.
     */
    public static boolean isNumeric(final String strNum) {
        final Pattern pattern = Pattern.compile("-?\\d+(\\.\\d+)?");

        if (strNum == null) {
            return false;
        }
        return pattern.matcher(strNum).matches();
    }

    /**
     * Creates a comma-separated String from a collection.
     *
     * @param c the collection
     * @return the String, empty if c is empty
     */
    public static String printCollection(final Collection<?> c) {
        if (c.isEmpty()) {
            return "";
        }

        String res = "";

        for (final Object obj : c) {
            res += obj.toString() + ",";
        }

        res = res.substring(0, res.length() - 1);

        return res;
    }

    /**
     * Removes whitespace from String.
     *
     * @param s the String
     * @return new String, s without whitespace
     */
    public static String removeWhitespace(final String s) {
        return s.replaceAll("\\s+", "");
    }

    /**
     * Separates a String along a given separator, preserves ordering.
     *
     * @param separator the separator
     * @param paramString the string to be separated
     * @return a list of the separated strings
     */
    public static List<String> separate(final String separator, final String paramString) {
        final String string = StringUtils.removeWhitespace(paramString);
        final String[] substrings = string.split(separator);

        final List<String> res = new LinkedList<String>();
        for (final String substring : substrings) {
            res.add(substring);
        }

        return res;
    }
}
