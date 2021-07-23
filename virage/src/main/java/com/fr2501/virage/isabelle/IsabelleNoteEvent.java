package com.fr2501.virage.isabelle;

import java.util.Map;

/**
 * An {@link IsabelleEvent} raised by Isabelle for informing the user about intermediate changes,
 * e.g. progress of a command.
 *
 * @author VeriVote
 */
public class IsabelleNoteEvent extends IsabelleEvent {
    /**
     * Siple constructor.
     * @param parameters the parameters.
     */
    public IsabelleNoteEvent(final Map<String, String> parameters) {
        super(parameters);
    }

}
