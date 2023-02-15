package com.fr2501.virage.prolog;

/**
 * A simple parsing interface for handling single Prolog clauses.
 *
 * @author VeriVote
 */
public interface PrologParser {
    /**
     * The Prolog file extension.
     */
    String PROLOG_FILE_EXTENSION = ".pl";

    /**
     * Parses a single Prolog predicate.
     *
     * @param predicate the predicate to be parsed
     * @return a {@link PrologPredicate} object representing that predicate
     */
    PrologPredicate parsePredicate(String predicate);

    /**
     * Parses a single Prolog clause.
     *
     * @param clause the clause to be parsed
     * @return a {@link PrologClause} object representing that clause
     */
    PrologClause parseSingleClause(String clause);
}
