package com.fr2501.virage.isabelle;

import com.fr2501.virage.prolog.PrologPredicate;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

/**
 * 
 * This class contains some useful utility functions for interaction with
 * Isabelle.
 *
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
  public static final String[] SIMPLE_TYPES = { "Nat.nat", "HOL.bool" };

  /**
   * String used by Isabelle to denote the line stating imported theories.
   */
  public static final String IMPORTS = "imports";

  /**
   * This method tries, along with other things, to match Prolog predicates to
   * Isabelle entities. It is case-insensitive, so no two Isabelle entities may
   * share the same name with different capitalization.
   * 
   * @param functionsAndDefinitions all functions and definitions given within the
   *                                current Isabelle folder
   * @param predicate               the predicate to be mapped
   * @return a map containing the Isabelle String and a set of all files that need
   *         to be imported for it to be fully known in the current file
   */
  public static Map<String, Set<String>> translatePrologToIsabelle(
      Map<String, String> functionsAndDefinitions,
      String predicate) {
    Set<String> requiredFiles = new HashSet<String>();

    String res = predicate.replace(",", ")(");
    res = res.replace("(", " (");

    Pattern pattern = Pattern.compile("[a-zA-Z_]+");
    Matcher matcher = pattern.matcher(res);

    while (matcher.find()) {
      String match = res.substring(matcher.start(), matcher.end());
      String replacement = match;

      for (String string : functionsAndDefinitions.keySet()) {
        if (string.equalsIgnoreCase(match)) {
          replacement = string;
          requiredFiles.add(functionsAndDefinitions.get(string));
          break;
        }
      }

      res = res.replace(match, replacement);
    }

    Map<String, Set<String>> resMap = new HashMap<String, Set<String>>();
    resMap.put(res, requiredFiles);
    return resMap;
  }

  /**
   * This method tries, along with other things, to match Prolog predicates to
   * Isabelle entities. It is case-insensitive, so no two Isabelle entities may
   * share the same name with different capitalization.
   * 
   * @param functionsAndDefinitions all functions and definitions given within the
   *                                current Isabelle folder
   * @param predicate               the predicate to be mapped
   * @return a map containing the Isabelle String and a set of all files that need
   *         to be imported for it to be fully known in the current file
   */
  public static Map<String, Set<String>> translatePrologToIsabelle(
      Map<String, String> functionsAndDefinitions,
      PrologPredicate predicate) {
    return translatePrologToIsabelle(functionsAndDefinitions, predicate.toString());
  }

  /**
   * Uses {@link IsabelleUtils#SIMPLE_TYPES} to determine whether the given type
   * is a simple Isabelle type.
   * 
   * @param type the type
   * @return true if type is simple type, false otherwise
   */
  public static boolean isSimpleType(String type) {
    for (String standardType : SIMPLE_TYPES) {
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
  public static String getUnusedVariable(String statement) {
    String unused = "x";

    if (!statement.contains(unused)) {
      return unused;
    }

    for (int i = 1; true; i++) {
      if (!statement.contains(unused + i)) {
        return unused + i;
      }
    }
  }
}
