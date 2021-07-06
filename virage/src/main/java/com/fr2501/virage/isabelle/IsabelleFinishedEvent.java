package com.fr2501.virage.isabelle;

import java.util.Map;

/**
 * An {@link IsabelleEvent} raised when a command finishes (not necessarily successful).
 *
 */
public class IsabelleFinishedEvent extends IsabelleEvent {

    public IsabelleFinishedEvent(Map<String, String> parameters) {
        super(parameters);
    }

    @Override
    public void applyEffects(IsabelleProofChecker checker) {
        checker.setFinished(true);
    }
}
