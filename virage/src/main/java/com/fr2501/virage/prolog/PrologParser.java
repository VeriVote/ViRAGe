package com.fr2501.virage.prolog;

/**
 * 
 * A simple parsing interface for handling single Prolog clauses.
 *
 */
public interface PrologParser {
  /**
   * Parses a single Prolog clause.
   * 
   * @param clause the clause to be parsed
   * @return a {@link PrologClause} object representing that clause
   */
  public PrologClause parseSingleClause(String clause);

  /**
   * Parses a single Prolog predicate.
   * 
   * @param predicate the predicate to be parsed
   * @return a {@link PrologPredicate} object representing that predicate
   */
  public PrologPredicate parsePredicate(String predicate);
}
