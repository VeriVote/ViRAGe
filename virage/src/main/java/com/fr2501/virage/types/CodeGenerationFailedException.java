package com.fr2501.virage.types;

/**
 * Exception wrapping different causes of code generation failure.
 * @author VeriVote
 *
 */
public final class CodeGenerationFailedException extends Exception {

    /**
     * The UID.
     */
    private static final long serialVersionUID = -6522608677098704720L;

    /**
     * The causing Exception.
     */
    private final Exception causeField;

    /**
     * Simple constructor.
     * @param cause the causing Exception
     */
    public CodeGenerationFailedException(final Exception cause) {
        this.causeField = cause;
    }

    @Override
    public String getMessage() {
        return "Code generation failed: " + this.causeField.getMessage();
    }

}
