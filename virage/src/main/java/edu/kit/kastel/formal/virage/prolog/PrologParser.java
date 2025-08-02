package edu.kit.kastel.formal.virage.prolog;

import edu.kit.kastel.formal.util.StringUtils;

/**
 * A simple parsing interface for handling single Prolog clauses.
 *
 * @author VeriVote
 */
public interface PrologParser {
    /**
     * Prolog neck directive.
     */
    String NECK = ":-";

    /**
     * The file ending for Prolog files (<code>*.pl</code>).
     */
    String DOT_PL = StringUtils.PERIOD + "pl";

    /**
     * SWI Prolog as string.
     */
    String SWI_PROLOG = "SWI Prolog";

    /**
     * EPL file as string.
     */
    String EPL_FILE = "(extended) Prolog file";

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
