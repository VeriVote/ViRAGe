package edu.kit.kastel.formal.virage.prolog;

/**
 * Saves which part of the extended Prolog file is currently handled.
 *
 * @author VeriVote
 */
public enum ParserState {
    /**
     * Several states the parser can be in, corresponding to the sections in an (E)PL file.
     */
    STARTING,

    /**
     * A framework component.
     */
    FRAMEWORK_COMPONENT,

    /**
     * A composition type.
     */
    COMPOSITION_TYPE,

    /**
     * A module that can be composed.
     * <b>Warning:</b> This was set to deprecated with no explicit justification,
     * maybe handle with care.
     */
    COMPOSABLE_MODULE,

    /**
     * A structure for composing modules.
     * <b>Warning:</b> This was set to deprecated with no explicit justification,
     * maybe handle with care.
     */
    COMPOSITIONAL_STRUCTURE,

    /**
     * A module property, for example a social choice property such as monotonicity, majority or
     * reinforcement.
     */
    PROPERTY,

    /**
     * A rule that allows to infer properties from a composition of modules.
     */
    COMPOSITION_RULE,
}
