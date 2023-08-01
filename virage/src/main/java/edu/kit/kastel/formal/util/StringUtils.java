package edu.kit.kastel.formal.util;

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
     * Checkstyle pleaser.
     */
    public static final String SPACE = " ";

    /**
     * A period sign.
     */
    public static final String PERIOD = ".";

    /**
     * A tab sign.
     */
    public static final String TAB = "\t";

    /**
     * Checkstyle pleaser.
     */
    public static final String ESCAPED_QUOTATION_MARK = "\"";

    /**
     * Base 64 hexadecimal code.
     */
    private static final int BASE_64 = 0x10000;

    /**
     * Strip the given command String.
     * @param command the potentially dangerous command String
     * @return the stripped command String
     */
    public static String strip(final String command) {
        return command.replaceAll("[;&|`]*", "");
    }

    /**
     * Escape the given command String.
     * @param command the potentially dangerous command String
     * @return the escaped command String
     */
    public static String escape(final String command) {
        return  command.replaceAll("[;&|`]+",
                                   "\\u" + Integer.toHexString('/' | BASE_64)
                                           .substring(1));
    }

    /**
     * Sanitize a given command String to avoid code injections or similar.
     * @param command the potentially dangerous command String
     * @return the sanitized command String
     */
    public static String stripAndEscape(final String command) {
        return escape(strip(command)).replaceAll("[\r\n]", "");
    }

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

        final StringBuilder res = new StringBuilder("");
        for (final Object obj : c) {
            res.append(obj).append(",");
        }
        return res.deleteCharAt(res.length() - 1).toString();
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

    /**
     * Puts parentheses around a String.
     * @param s the string
     * @return (s)
     */
    public static String parenthesize(final String s) {
        return "(" + s + ")";
    }

    /**
     * Indents a String by a single tab.
     * @param s the string
     * @return \ts
     */
    public static String indentWithTab(final String s) {
        return TAB + s;
    }

    /**
     * Appends a period to a String.
     * @param s the string
     * @return s.
     */
    public static String appendPeriod(final String s) {
        return s + PERIOD;
    }
}
