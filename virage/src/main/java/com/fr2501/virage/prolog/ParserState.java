package com.fr2501.virage.prolog;

/**
 * Saves which part of the extended Prolog file is currently handled.
 *
 * @author VeriVote
 */
public enum ParserState {
    /**
     * Several states the parser can be in, corresponding to the sections in an (E)PL file.
     */
    STARTING, FRAMEWORK_COMPONENT, COMPOSITION_TYPE,

    /**
     * Checkstyle comment.
     * <b>Warning:</b> This was set to deprecated with no explicit justification,
     * maybe handle with care.
     */
    COMPOSABLE_MODULE,

    /**
     * Checkstyle comment.
     * <b>Warning:</b> This was set to deprecated with no explicit justification,
     * maybe handle with care.
     */
    COMPOSITIONAL_STRUCTURE,

    /**
     * TODO.
     */
    PROPERTY,

    /**
     * TODO.
     */
    COMPOSITION_RULE,
}
