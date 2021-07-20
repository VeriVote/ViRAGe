package com.fr2501.virage.isabelle;

import java.util.Map;

/**
 * An {@link IsabelleEvent} raised by Isabelle for informing the user about intermediate changes,
 * e.g. progress of a command.
 *
 */
public class IsabelleNoteEvent extends IsabelleEvent {

    public IsabelleNoteEvent(final Map<String, String> parameters) {
        super(parameters);
    }

}
