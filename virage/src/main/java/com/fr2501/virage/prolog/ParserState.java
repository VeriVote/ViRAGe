package com.fr2501.virage.prolog;

/**
 * Saves which part of the extended Prolog file is currently handled.
 *
 */
public enum ParserState {
    /**
     * Several states the parser can be in, corresponding to the sections in an (E)PL file.
     */
    STARTING, FRAMEWORK_COMPONENT, COMPOSITION_TYPE,
    /**
     * (Checkstyle comment.
     */
    @Deprecated COMPOSABLE_MODULE,
    /**
     * Checkstyle comment.
     */
    @Deprecated COMPOSITIONAL_STRUCTURE, PROPERTY, COMPOSITION_RULE,
}
