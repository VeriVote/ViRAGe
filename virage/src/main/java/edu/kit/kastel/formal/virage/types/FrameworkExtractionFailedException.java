package edu.kit.kastel.formal.virage.types;

/**
 * Exception wrapping different causes of code generation failure.
 * @author VeriVote
 *
 */
public final class FrameworkExtractionFailedException extends Exception {

    /**
     * The UID.
     */
    private static final long serialVersionUID = 3807566376963237704L;

    /**
     * The causing Exception.
     */
    private final Exception causeField;

    /**
     * Simple constructor.
     * @param cause the causing Exception
     */
    public FrameworkExtractionFailedException(final Exception cause) {
        this.causeField = cause;
    }

    @Override
    public String getMessage() {
        return "Framework extraction failed: " + this.causeField.getMessage();
    }

}
