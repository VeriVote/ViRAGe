package com.fr2501.virage.types;

/**
 * Signals a mismatch of program and config file version.
 *
 */
public class InvalidConfigVersionException extends RuntimeException {

    /**
     * Generated ID.
     */
    private static final long serialVersionUID = 6116199849357596875L;

    /**
     * Simple constructor.
     * @param message the message
     */
    public InvalidConfigVersionException(final String message) {
        super(message);
    }
}
