package edu.kit.kastel.formal.virage.types;

/**
 * A type to represent logical values of different confidence levels.
 *
 * @author VeriVote
 */
public enum BooleanWithUncertainty {
    /**
     * Equivalent to Boolean.TRUE.
     */
    TRUE,
    /**
     * Uncertain, but slightly stronger than MAYBE.
     */
    MAYBE_NO_COUNTEREXAMPLE_FOUND,
    /**
     * Uncertain.
     */
    MAYBE,
    /**
     * Equivalent to Boolean.FALSE.
     */
    FALSE
}
