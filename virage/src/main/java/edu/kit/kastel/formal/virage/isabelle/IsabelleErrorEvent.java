package edu.kit.kastel.formal.virage.isabelle;

import java.util.Map;

/**
 * Is raised whenever the Isabelle CLI throws errors.
 *
 * @author VeriVote
 */
public class IsabelleErrorEvent extends IsabelleEvent {
    /**
     * Simple constructor.
     * @param parameters the parameters
     */
    public IsabelleErrorEvent(final Map<String, String> parameters) {
        super(parameters);
    }

}
