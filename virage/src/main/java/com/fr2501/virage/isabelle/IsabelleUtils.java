package com.fr2501.virage.isabelle;

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

import com.fr2501.util.SimpleFileReader;
import com.fr2501.virage.prolog.PrologPredicate;

/**
 * This class contains some useful utility functions for interaction with Isabelle.
 *
 * @author VeriVote
 */
public class IsabelleUtils {
    /**
     * String used by Isabelle to mark Exceptions in its commands.
     */
    public static final String EXCEPTION = "Exception";

    /**
     * File extension for Isabelle theory files.
     */
    public static final String FILE_EXTENSION = ".thy";

    /**
     * String used by Isabelle to denote successful termination.
     */
    public static final String SUCCESS_STRING = "OK ";

    // TODO: Add all types
    /**
     * Simple types offered by Isabelle/HOL.
     */
    public static final String[] SIMPLE_TYPES = {"Nat.nat", "HOL.bool"};

    /**
     * String used by Isabelle to denote the line stating imported theories.
     */
    public static final String IMPORTS = "imports";

    /**
     * String used by Isabelle in type signatures.
     */
    public static final String RIGHTARROW = "=>";

    /**
     * String used by Isabelle for anonymous types.
     */
    public static final String TYPE_ALIAS = "'a";

    /**
     * Isabelle ROOT keyword.
     */
    public static final String ROOT = "ROOT";

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

        String res = predicate.replace(",", ")(");
        res = res.replace("(", " (");

        final Pattern pattern = Pattern.compile("[a-zA-Z_]+");
        final Matcher matcher = pattern.matcher(res);

        while (matcher.find()) {
            final String match = res.substring(matcher.start(), matcher.end());
            String replacement = match;

            for (final String string : functionsAndDefinitions.keySet()) {
                if (string.equalsIgnoreCase(match)) {
                    replacement = string;
                    requiredFiles.add(functionsAndDefinitions.get(string));
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
        for (final String standardType : SIMPLE_TYPES) {
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
        final String unused = "x";

        if (!statement.contains(unused)) {
            return unused;
        }

        for (int i = 1; true; i++) {
            if (!statement.contains(unused + i)) {
                return unused + i;
            }
        }
    }

    public static List<String> getSessionNamesFromRootFile(final File root) throws IOException {
        final List<String> res = new LinkedList<String>();

        final SimpleFileReader reader = new SimpleFileReader();
        final List<String> lines = reader.readFileByLine(root);

        final Pattern pattern = Pattern.compile("session[\\s]+(.*)[\\s]+=.*");

        for(final String line: lines) {
            final Matcher matcher = pattern.matcher(line);

            if(matcher.matches()) {
                res.add(matcher.group(1));
            }
        }

        return res;
    }
}
