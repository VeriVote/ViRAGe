package edu.kit.kastel.formal.virage.types;

import java.io.IOException;

/**
 * Exception to be raised when a settings entry cannot be parsed.
 *
 * @author VeriVote
 */
public class MalformedSettingsValueException extends IOException {
    /**
     * The UID.
     */
    private static final long serialVersionUID = 3566709391218079822L;

    /**
     * The malformed value that triggered this exception.
     */
    private final String malformedValue;

    /**
     * Simple constructor.
     *
     * @param newMalformedValue the malformed value causing the exception.
     */
    public MalformedSettingsValueException(final String newMalformedValue) {
        this.malformedValue = newMalformedValue;
    }

    @Override
    public final String getMessage() {
        return "Malformed setting value: " + this.malformedValue;
    }
}
