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
     * A question mark.
     */
    public static final String QUESTION = "?";

    /**
     * A dash sign.
     */
    public static final String DASH = "-";

    /**
     * A hash sign.
     */
    public static final String HASH = "#";

    /**
     * A star sign.
     */
    public static final String STAR = "*";

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
    public static final int THREE = 3;

    /**
     * The number five.
     */
    public static final int FIVE = 5;

    /**
     * The number ten.
     */
    public static final int TEN = 10;

    /**
     * An opening bracket sign.
     */
    private static final String OPENING_BRACKET = "]";

    /**
     * A closing bracket sign.
     */
    private static final String CLOSING_BRACKET = "[";

    /**
     * The disjunction (or) sign.
     */
    private static final String OR = "or";

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
        final StringBuilder res = new StringBuilder();
        for (final Object obj: c) {
            res.append(obj).append(COMMA.charAt(0));
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
        final StringBuilder res = new StringBuilder();
        for (final Object obj: c) {
            res.append(obj).append(SPACE.charAt(0));
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
     * Adds a space as prefix before the given String.
     *
     * @param s the given String.
     * @return new String with added space in the beginning
     */
    public static String prefixSpace(final String s) {
        return SPACE + s;
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
     * Adds one space before and one after the given String.
     *
     * @param s the given String.
     * @return new String with added spaces before and after
     */
    public static String surroundWithSpaces(final String s) {
        return SPACE + s + SPACE;
    }

    /**
     * Adds the separator and a space before and a space and the separator after the given String.
     *
     * @param s the given String.
     * @param separator the separator.
     * @return new String with added separator and spaces before and after
     */
    public static String surroundWithSpacedSeparators(final String s, final String separator) {
        return separator + surroundWithSpaces(s) + separator;
    }

    /**
     * Put the given String in a raw Isabelle comment.
     *
     * @param s the given String.
     * @return the resulting Isabelle comment containing the given String
     */
    public static String isabelleComment(final String s) {
        return parenthesize(surroundWithSpacedSeparators(s, STAR));
    }

    /**
     * Put the given String in a raw Isabelle comment line.
     *
     * @param s the given String.
     * @return the resulting Isabelle comment line containing the given String
     */
    public static String isabelleCommentLine(final String s) {
        return isabelleComment(s) + System.lineSeparator();
    }

    /**
     * Put the given Strings in raw Isabelle comment lines.
     *
     * @param s the given Strings.
     * @return the resulting Isabelle comment lines containing the given Strings
     */
    public static String isabelleCommentLines(final String... s) {
        final StringBuilder sb = new StringBuilder();
        for (final String s1: s) {
            sb.append(isabelleCommentLine(s1));
        }
        return sb.toString();
    }

    /**
     * Put the given Strings in raw Isabelle comment block.
     *
     * @param s the given Strings.
     * @return the resulting Isabelle comment block containing the given Strings
     */
    public static String isabelleCommentBlock(final String... s) {
        final String starLine = parenthesize(repeat(22, addSpace(STAR)) + STAR);
        return starLine + System.lineSeparator() + isabelleCommentLines(s) + starLine;
    }

    /**
     * Returns a disjunction of the two string arguments.
     *
     * @param s1 the first argument
     * @param s2 the second argument
     * @return the disjunction of the two strings
     */
    public static String or(final String s1, final String s2) {
        return printCollection2(s1, OR, s2);
    }

    /**
     * Adds a colon after the given string.
     *
     * @param s the given String.
     * @return new String with added colon at the end
     */
    public static String addColon(final String s) {
        return s + COLON;
    }

    /**
     * Add single quotes around the string.
     *
     * @param string the given string
     * @return the string with single quotes around it
     */
    public static String addQuotations(final String string) {
        final String delimiter = "\'";
        return delimiter + string + delimiter;
    }

    /**
     * Adds double quotes around the string.
     *
     * @param string the given string
     * @return the string with double quotes around it
     */
    public static String addDoubleQuotes(final String string) {
        final String delimiter = StringUtils.QUOTATION;
        return delimiter + string + delimiter;
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
     * Puts brackets around a comma-separated list of strings.
     *
     * @param args the string arguments to bracketize
     * @return the bracketized string representation
     */
    public static String bracketize(final String... args) {
        return OPENING_BRACKET + printCollection(Arrays.asList(args)) + CLOSING_BRACKET;
    }

    /**
     * Puts parentheses around a comma-separated list of strings.
     *
     * @param args the string arguments to bracketize
     * @return the bracketized string representation
     */
    public static String bracketize(final Collection<String> args) {
        if (args == null || args.isEmpty()) {
            return EMPTY;
        }
        return bracketize(args.toArray(new String[args.size()]));
    }

    /**
     * Puts brackets around a space-separated list of strings.
     *
     * @param args the string arguments to bracketize
     * @return the bracketized string representation
     */
    public static String bracketize2(final String... args) {
        return OPENING_BRACKET + printCollection2(Arrays.asList(args)) + CLOSING_BRACKET;
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
        return addSpace(fun != null ? fun : EMPTY) + parenthesize2(args);
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
        return addSpace(fun != null ? fun : EMPTY)
                + addSpace(parenthesize2(arg1)) + parenthesize2(arg2);
    }

    /**
     * Returns map function string with two separately parenthesized arguments.
     *
     * @param fun the function which is to be applied by the map
     * @param app the collection argument to which the function is applied
     * @return the function string representation
     */
    public static String map(final String fun, final String app) {
        return map(MAP, fun, app);
    }

    /**
     * Repeats a string 'm' times if 'm' is nonnegative, otherwise return null.
     *
     * @param m the amount of tabs to indent
     * @param s the string
     * @return the repeated string
     */
    public static String repeat(final int m, final String s) {
        final String res;
        if (m < 0) {
            res = null;
        } else {
            final StringBuilder r = new StringBuilder();
            for (int i = 0; i < m; i++) {
                r.append(s);
            }
            res = r.toString();
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
     * Appends a question mark to a string.
     *
     * @param s the string
     * @return s?
     */
    public static String appendQuestionMark(final String s) {
        return s + QUESTION;
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
        return appendPeriod(s) + System.lineSeparator();
    }
}
