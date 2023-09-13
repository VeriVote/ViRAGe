package edu.kit.kastel.formal.util;

import java.util.Arrays;
import java.util.Collection;
import java.util.LinkedList;
import java.util.List;
import java.util.regex.Pattern;

/**
 * A collection of useful String utilities.
 *
 * @author VeriVote
 */
public final class StringUtils {
    /**
     * A space.
     */
    public static final String SPACE = " ";

    /**
     * A period sign.
     */
    public static final String PERIOD = ".";

    /**
     * A hash sign.
     */
    public static final String HASH = "#";

    /**
     * An opening parenthesis sign.
     */
    public static final String OPENING_PARENTHESIS = "(";

    /**
     * A closing parenthesis sign.
     */
    public static final String CLOSING_PARENTHESIS = ")";

    /**
     * A tab sign.
     */
    public static final String TAB = "\t";

    /**
     * An escaped quotation mark.
     */
    public static final String QUOTATION = "\"";

    /**
     * An empty string.
     */
    public static final String EMPTY = "";

    /**
     * String representation of a comma sign.
     */
    public static final String COMMA = ",";

    /**
     * The colon sign.
     */
    public static final String COLON = ":";

    /**
     * The caret sign.
     */
    public static final String CARET = "^";

    /**
     * The equality sign.
     */
    public static final String EQ = "=";

    /**
     * A space character.
     */
    public static final char SPACE_CHAR = ' ';

    /**
     * Dot character.
     */
    public static final char DOT_CHAR = '.';

    /**
     * Comma character.
     */
    public static final char COMMA_CHAR = ',';

    /**
     * Left (opening) parenthesis.
     */
    public static final char LEFT_PAREN = '(';

    /**
     * Right (closing) parenthesis.
     */
    public static final char RIGHT_PAREN = ')';

    /**
     * The number three.
     */
    private static final int THREE = 3;

    /**
     * String for map function.
     */
    private static final String MAP = "map";

    /**
     * Base 64 hexadecimal code.
     */
    private static final int BASE_64 = 0x10000;

    private StringUtils() { }

    /**
     * Strip the given command String.
     *
     * @param command the potentially dangerous command String
     * @return the stripped command String
     */
    public static String strip(final String command) {
        return command.replaceAll("[;&|`]*", EMPTY);
    }

    /**
     * Escape the given command String.
     *
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
     *
     * @param command the potentially dangerous command String
     * @return the sanitized command String
     */
    public static String stripAndEscape(final String command) {
        return escape(strip(command)).replaceAll("[\r\n]", EMPTY);
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
            return EMPTY;
        }
        final StringBuilder res = new StringBuilder(EMPTY);
        for (final Object obj: c) {
            res.append(obj).append(COMMA);
        }
        return res.deleteCharAt(res.length() - 1).toString();
    }

    /**
     * Creates a comma-separated String from a variable number of arguments.
     *
     * @param c the collection
     * @return the String, empty if c is empty
     */
    public static String printCollection(final String... c) {
        return printCollection(Arrays.asList(c));
    }

    /**
     * Creates a space-separated String from a collection.
     *
     * @param c the collection
     * @return the String, empty if c is empty
     */
    public static String printCollection2(final Collection<?> c) {
        if (c.isEmpty()) {
            return EMPTY;
        }
        final StringBuilder res = new StringBuilder(EMPTY);
        for (final Object obj: c) {
            res.append(obj).append(SPACE);
        }
        return res.deleteCharAt(res.length() - 1).toString();
    }

    /**
     * Creates a space-separated String from a variable number of arguments.
     *
     * @param c the collection
     * @return the String, empty if c is empty
     */
    public static String printCollection2(final String... c) {
        return printCollection2(Arrays.asList(c));
    }

    /**
     * Removes whitespace from String.
     *
     * @param s the String
     * @return new String s without whitespace
     */
    public static String removeWhitespace(final String s) {
        return s.replaceAll("\\s+", EMPTY);
    }

    /**
     * Adds a space after the given String.
     *
     * @param s the given String.
     * @return new String with added space at the end
     */
    public static String addSpace(final String s) {
        return s + SPACE;
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
        for (final String substring: substrings) {
            res.add(substring);
        }
        return res;
    }

    /**
     * Puts parentheses around a comma-separated list of strings.
     *
     * @param args the string arguments to parenthesize
     * @return the parenthesized string representation
     */
    public static String parenthesize(final String... args) {
        return OPENING_PARENTHESIS + printCollection(Arrays.asList(args)) + CLOSING_PARENTHESIS;
    }

    /**
     * Puts parentheses around a comma-separated list of strings.
     *
     * @param args the string arguments to parenthesize
     * @return the parenthesized string representation
     */
    public static String parenthesize(final Collection<String> args) {
        if (args == null || args.isEmpty()) {
            return EMPTY;
        }
        return parenthesize(args.toArray(new String[args.size()]));
    }

    /**
     * Puts parentheses around a space-separated list of strings.
     *
     * @param args the string arguments to parenthesize
     * @return the parenthesized string representation
     */
    public static String parenthesize2(final String... args) {
        return OPENING_PARENTHESIS + printCollection2(Arrays.asList(args)) + CLOSING_PARENTHESIS;
    }

    /**
     * Returns function string with a variable amount of argument.
     *
     * @param fun the function name
     * @param args the arguments of the function
     * @return the function string representation
     */
    public static String func(final String fun, final String... args) {
        return (fun != null ? fun : EMPTY) + parenthesize(args);
    }

    /**
     * Returns function string with a variable amount of arguments.
     *
     * @param fun the function name
     * @param args the arguments of the function
     * @return the function string representation
     */
    public static String func2(final String fun, final String... args) {
        return (fun != null ? fun : EMPTY) + SPACE + parenthesize2(args);
    }

    /**
     * Returns map-like function string with two separately parenthesized arguments.
     *
     * @param fun the function name
     * @param arg1 the function which is to be applied by the map-like function
     * @param arg2 the collection argument to which the function is applied
     * @return the function string representation
     */
    public static String map(final String fun, final String arg1, final String arg2) {
        return (fun != null ? fun : EMPTY) + SPACE
                + parenthesize2(arg1) + SPACE + parenthesize2(arg2);
    }

    /**
     * Returns map function string with two separately parenthesized arguments.
     *
     * @param arg1 the function which is to be applied by the map
     * @param arg2 the collection argument to which the function is applied
     * @return the function string representation
     */
    public static String map(final String arg1, final String arg2) {
        return map(MAP, arg1, arg2);
    }

    /**
     * Repeats a string 'm' times if 'm' is nonnegative, otherwise return null.
     *
     * @param m the amount of tabs to indent
     * @param s the string
     * @return the repeated string
     */
    public static String repeat(final int m, final String s) {
        String res;
        if (m < 0) {
            res = null;
        } else {
            res = EMPTY;
            for (int i = 0; i < m; i++) {
                res += s;
            }
        }
        return res;
    }

    /**
     * Indents a string by 'm' tabs if 'm' is nonnegative, otherwise return null.
     *
     * @param m the amount of tabs to indent
     * @param s the string
     * @return the indented string
     */
    public static String indentWithTabs(final int m, final String s) {
        String res;
        if (m < 0) {
            res = null;
        } else {
            res = s;
            for (int i = 0; i < m; i++) {
                res = TAB + res;
            }
        }
        return res;
    }

    /**
     * Indents a string by three tabs.
     *
     * @param s the string
     * @return the indented string
     */
    public static String indentWithThreeTab(final String s) {
        return indentWithTabs(THREE, s);
    }

    /**
     * Indents a string by a single tab.
     *
     * @param s the string
     * @return the indented string
     */
    public static String indentWithTab(final String s) {
        return indentWithTabs(1, s);
    }

    /**
     * Appends a period to a string.
     *
     * @param s the string
     * @return s.
     */
    public static String appendPeriod(final String s) {
        return s + PERIOD;
    }

    /**
     * Appends a period and a line break to a string.
     *
     * @param s the string
     * @return s.\n
     */
    public static String sentence(final String s) {
        return s + PERIOD + System.lineSeparator();
    }
}
