package edu.kit.kastel.formal.virage.types;

/**
 * An exception thrown if compilation of generated code fails.
 *
 *  @author VeriVote
 */
public class CompilationFailedException extends Exception {
    /**
     * The UID.
     */
    private static final long serialVersionUID = -3356300070323059173L;

    /**
     * The message of this exception.
     */
    private final String message;

    /**
     * Simple constructor.
     *
     * @param msg the message
     */
    public CompilationFailedException(final String msg) {
        this.message = msg;
    }

    /**
     * Safe to override.
     */
    @Override
    public String getLocalizedMessage() {
        return this.message;
    }

    /**
     * Safe to override.
     */
    @Override
    public String getMessage() {
        return this.message;
    }
}
