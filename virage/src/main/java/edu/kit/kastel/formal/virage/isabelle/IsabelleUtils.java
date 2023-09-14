package edu.kit.kastel.formal.virage.isabelle;

import java.io.File;
import java.io.IOException;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import edu.kit.kastel.formal.util.SimpleFileReader;
import edu.kit.kastel.formal.util.StringUtils;
import edu.kit.kastel.formal.virage.prolog.PrologPredicate;

/**
 * This class contains some useful utility functions for interaction with Isabelle.
 *
 * @author VeriVote
 */
public final class IsabelleUtils {
    /**
     * String used by Isabelle to mark Exceptions in its commands.
     */
    public static final String EXCEPTION = "Exception";

    /**
     * File extension for Isabelle theory files.
     */
    public static final String DOT_THY = StringUtils.PERIOD + "thy";

    /**
     * File extension for LaTeX files.
     */
    public static final String DOT_TEX = StringUtils.PERIOD + "tex";

    /**
     * String used by Isabelle to denote successful termination.
     */
    public static final String SUCCESS_STRING = "OK ";

    /**
     * String used by Isabelle to denote the line stating imported theories.
     */
    public static final String IMPORTS = "imports";

    /**
     * String used by Isabelle in type signatures.
     */
    public static final String RIGHT_ARROW = "=>";

    /**
     * String used by Isabelle for anonymous types.
     */
    public static final String TYPE_ALIAS = "'a";

    /**
     * String "A".
     */
    public static final String DEFAULT_SET = "A";

    /**
     * Isabelle ROOT keyword.
     */
    public static final String ROOT = "ROOT";

    /**
     * The name of Isabelle type "fun".
     */
    public static final String FUN = "fun";

    /**
     * The Isabelle proof command 'by'.
     */
    public static final String BY = "by";

    /**
     * String used to separate session and theory names.
     */
    public static final String THEORY_NAME_SEPARATOR = StringUtils.PERIOD;

    /**
     * Higher-order logic theory.
     */
    public static final String HOL = "HOL";

    /**
     * Isabelle's set theory.
     */
    public static final String SET = "Set";

    /**
     * String to represent the HOL type for natural numbers.
     */
    public static final String NAT = "Nat" + THEORY_NAME_SEPARATOR + "nat";

    /**
     * String to represent the HOL boolean type.
     */
    public static final String BOOL = HOL + THEORY_NAME_SEPARATOR + "bool";

    // TODO: Add all types
    /**
     * Simple types offered by Isabelle/HOL.
     */
    private static final String[] SIMPLE_TYPES = {NAT, BOOL};

    private IsabelleUtils() { }

    /**
     * This method tries, along with other things, to match Prolog predicates to Isabelle entities.
     * It is case-insensitive, so no two Isabelle entities may share the same name with different
     * capitalization.
     *
     * @param functionsAndDefinitions all functions and definitions given within the current
     *      Isabelle folder
     * @param predicate the predicate to be mapped
     * @return a map containing the Isabelle String and a set of all files that need to be imported
     *       for it to be fully known in the current file
     */
    public static Map<String, Set<String>> translatePrologToIsabelle(
            final Map<String, String> functionsAndDefinitions, final String predicate) {
        final Set<String> requiredFiles = new HashSet<String>();
        String res = predicate.replace(",",
                StringUtils.CLOSING_PARENTHESIS + StringUtils.OPENING_PARENTHESIS);
        res = res.replace(StringUtils.OPENING_PARENTHESIS,
                          StringUtils.prefixSpace(StringUtils.OPENING_PARENTHESIS));
        final Pattern pattern = Pattern.compile("[a-zA-Z_]+");
        final Matcher matcher = pattern.matcher(res);
        while (matcher.find()) {
            final String match = res.substring(matcher.start(), matcher.end());
            String replacement = match;
            for (final Map.Entry<String, String> entry: functionsAndDefinitions.entrySet()) {
                if (entry.getKey().equalsIgnoreCase(match)) {
                    replacement = entry.getKey();
                    requiredFiles.add(entry.getValue());
                    break;
                }
            }
            res = res.replace(match, replacement);
        }
        final Map<String, Set<String>> resMap = new HashMap<String, Set<String>>();
        resMap.put(res, requiredFiles);
        return resMap;
    }

    /**
     * This method tries, along with other things, to match Prolog predicates to Isabelle entities.
     * It is case-insensitive, so no two Isabelle entities may share the same name with different
     * capitalization.
     *
     * @param functionsAndDefinitions all functions and definitions given within the current
     *      Isabelle folder
     * @param predicate the predicate to be mapped
     * @return a map containing the Isabelle String and a set of all files that need to be imported
     *      for it to be fully known in the current file
     */
    public static Map<String, Set<String>> translatePrologToIsabelle(
            final Map<String, String> functionsAndDefinitions, final PrologPredicate predicate) {
        return translatePrologToIsabelle(functionsAndDefinitions, predicate.toString());
    }

    /**
     * Uses {@link IsabelleUtils#SIMPLE_TYPES} to determine whether the given type is a simple
     * Isabelle type.
     *
     * @param type the type
     * @return true if type is simple type, false otherwise
     */
    public static boolean isSimpleType(final String type) {
        for (final String standardType: SIMPLE_TYPES) {
            if (standardType.equals(type)) {
                return true;
            }
        }
        return false;
    }

    /**
     * Finds a new Isabelle variable not yet used within the given statement.
     *
     * @param statement the statement
     * @return a new variable ('x' if possible, otherwise tries 'x1', 'x2', ...)
     */
    public static String getUnusedVariable(final String statement) {
        final String unused = ScalaIsabelleFacade.DEFAULT_VARIABLE;
        if (!statement.contains(unused)) {
            return unused;
        }
        for (int i = 1; true; i++) {
            if (!statement.contains(unused + i)) {
                return unused + i;
            }
        }
    }

    /**
     * Extracts session names from a ROOT file.
     * @param root the ROOT file
     * @return the sessions defined within it
     * @throws IOException if IO operations fail
     */
    public static List<String> getSessionNamesFromRootFile(final File root) throws IOException {
        final List<String> res = new LinkedList<String>();
        if (root.exists()) {
            final SimpleFileReader reader = new SimpleFileReader();
            final Pattern pattern = Pattern.compile("session[\\s]+(.*)[\\s]+=.*");
            for (final String line: reader.readFileByLine(root)) {
                final Matcher matcher = pattern.matcher(line);
                if (matcher.matches()) {
                    res.add(matcher.group(1));
                }
            }
        }
        return res;
    }
}
