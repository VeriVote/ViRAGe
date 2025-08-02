package edu.kit.kastel.formal.virage.types;

/**
 * Signals a mismatch of program and configuration file version.
 *
 * @author VeriVote
 */
public class InvalidConfigVersionException extends RuntimeException {
    /**
     * Generated ID.
     */
    private static final long serialVersionUID = 6116199849357596875L;

    /**
     * Simple constructor.
     *
     * @param message the message
     */
    public InvalidConfigVersionException(final String message) {
        super(message);
    }
}
