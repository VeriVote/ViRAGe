package edu.kit.kastel.formal.virage.prolog;

/**
 * The different states generic queries can end with.
 *
 * @author VeriVote
 */
public enum QueryState {
    /**
     * Time-out query.
     */
    TIMEOUT,

    /**
     * Failed query.
     */
    FAILED,

    /**
     * Erroneous query.
     */
    ERROR,

    /**
     * Successful query.
     */
    SUCCESS
}
