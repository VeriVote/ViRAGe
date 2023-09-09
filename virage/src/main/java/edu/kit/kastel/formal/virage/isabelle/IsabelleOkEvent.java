package edu.kit.kastel.formal.virage.isabelle;

import java.util.Map;

/**
 * An {@link IsabelleEvent} raised when a command finishes successfully, only applicable for some
 * commands. Others might raise an {@link IsabelleFinishedEvent} with a key-value pair
 * ("okay"="true").
 *
 * @author VeriVote
 */
public class IsabelleOkEvent extends IsabelleEvent {
    /**
     * Simple constructor.
     * @param parameters the parameters
     */
    public IsabelleOkEvent(final Map<String, String> parameters) {
        super(parameters);
    }
}
