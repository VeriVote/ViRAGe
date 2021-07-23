package com.fr2501.virage.isabelle;

import java.util.Map;

/**
 * An {@link IsabelleEvent} raised when a command finishes (not necessarily successful).
 *
 */
public final class IsabelleFinishedEvent extends IsabelleEvent {
    /**
     * Simple constructor.
     * @param parameters the parameters
     */
    public IsabelleFinishedEvent(final Map<String, String> parameters) {
        super(parameters);
    }

    @Override
    public void applyEffects(final IsabelleProofChecker checker) {
        checker.setFinished(true);
    }
}
