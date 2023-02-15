package com.fr2501.virage.isabelle;

import java.util.Map;

/**
 * An {@link IsabelleEvent} raised when a command finishes successfully, only applicable for some
 * commands. Others might raise an {@link IsabelleFinishedEvent} with key-value pair ("ok"="true").
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
