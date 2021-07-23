package com.fr2501.virage.isabelle;

import java.util.Map;

/**
 * A class to represent the events raised by the Isabelle CLI.
 *
 */
public abstract class IsabelleEvent {
    /**
     * The parameters.
     */
    private final Map<String, String> parameters;

    /**
     * Simple constructor.
     * @param parameters the parameters.
     */
    public IsabelleEvent(final Map<String, String> parameters) {
        this.parameters = parameters;
    }

    /**
     * Applies the effects of this event to its observer.
     *
     * @param observer The {@link IsabelleProofChecker} observing the event
     */
    public void applyEffects(final IsabelleProofChecker observer) {
        // default: no-op
    }

    /**
     * Returns the value of a given key.
     *
     * @param key the key
     * @return the value
     */
    public String getValue(final String key) {
        return this.parameters.get(key);
    }

    /**
     * Safe to override.
     */
    @Override
    public String toString() {
        String res = this.getClass().getCanonicalName();

        for (final String key : this.parameters.keySet()) {
            res += "\n\t" + key + ": " + this.parameters.get(key);
        }

        return res;
    }
}
