package edu.kit.kastel.formal.virage.isabelle;

import java.util.Map;

import edu.kit.kastel.formal.util.StringUtils;

/**
 * A class to represent the events raised by the Isabelle CLI.
 *
 * @author VeriVote
 */
public abstract class IsabelleEvent {
    /**
     * The parameters.
     */
    private final Map<String, String> parameters;

    /**
     * Simple constructor.
     * @param parametersValue the parameters.
     */
    public IsabelleEvent(final Map<String, String> parametersValue) {
        this.parameters = parametersValue;
    }

    /**
     * Applies the effects of this event to its observer.
     *
     * @param observer The {@link IsabelleProofChecker} observing the event
     */
    public void applyEffects(final IsabelleProofChecker observer) {
        // default: skip operation
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
        for (final Map.Entry<String, String> entry: this.parameters.entrySet()) {
            res += System.lineSeparator() + StringUtils.indentWithTab(entry.getKey())
                    + ": " + entry.getValue();
        }

        return res;
    }
}
