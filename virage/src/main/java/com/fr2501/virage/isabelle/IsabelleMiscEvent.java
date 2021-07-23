package com.fr2501.virage.isabelle;

import java.util.HashMap;
import java.util.Map;

/**
 * An {@link IsabelleEvent} raised whenever none of the concrete types fits the event.
 *
 */
public class IsabelleMiscEvent extends IsabelleEvent {
    /**
     * Simple constructor.
     */
    public IsabelleMiscEvent() {
        this(new HashMap<String, String>());
    }

    /**
     * Simple constructor.
     * @param parameters the parameters.
     */
    public IsabelleMiscEvent(final Map<String, String> parameters) {
        super(parameters);
    }

}
