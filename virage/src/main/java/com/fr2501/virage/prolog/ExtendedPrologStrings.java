package com.fr2501.virage.prolog;

/**
 * Magic strings required to parse the extended Prolog format.
 *
 * @author VeriVote
 */

public abstract class ExtendedPrologStrings {
    /**
     * Theory path prefix.
     */
    public static final String THEORY_PATH_PREFIX = "====";
    /**
     * Component type header.
     */
    public static final String COMPOSITION_TYPE_HEADER = "=== COMPONENT_TYPE";
    /**
     * Composable module header.
     */
    @Deprecated
    public static final String COMPOSABLE_MODULE_HEADER = "=== COMPOSABLE_MODULE";
    /**
     * Composable module string.
     */
    @Deprecated
    public static final String COMPOSABLE_MODULE = "COMPOSABLE_MODULE";
    /**
     * Compositional structure header.
     */
    @Deprecated
    public static final String COMPOSITIONAL_STRUCTURE_HEADER = "=== COMPOSITIONAL_STRUCTURE";
    /**
     * Property header.
     */
    public static final String PROPERTY_HEADER = "=== PROPERTY";
    /**
     * Composition rule header.
     */
    public static final String COMPOSITION_RULE_HEADER = "=== COMPOSITION_RULE";
    /**
     * Component string.
     */
    public static final String COMPONENT = "COMPONENT";

    /**
     * "Undefined" keyword.
     */
    public static final String UNDEFINED = "UNDEFINED";
    /**
     * "Assumption" keyword.
     */
    public static final String ASSUMPTION = "ASSUMPTION";
    /**
     * "Unproven" keyword.
     */
    public static final String UNPROVEN = "UNPROVEN";

    /**
     * Comment indicator.
     */
    public static final String COMMENT = "%";

    /**
     * The character used to indicate headers.
     */
    public static final String FORMATTER = "=";
}
