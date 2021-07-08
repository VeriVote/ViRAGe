package com.fr2501.virage.prolog;

/**
 * Magic strings required to parse the extended Prolog format.
 *
 */

public abstract class ExtendedPrologStrings {
    public static final String THEORY_PATH_PREFIX = "====";
    public static final String COMPOSITION_TYPE_HEADER = "=== COMPONENT_TYPE";
    public static final String COMPOSABLE_MODULE_HEADER = "=== COMPOSABLE_MODULE";
    public static final String COMPOSABLE_MODULE = "COMPOSABLE_MODULE";
    public static final String COMPOSITIONAL_STRUCTURE_HEADER = "=== COMPOSITIONAL_STRUCTURE";
    public static final String PROPERTY_HEADER = "=== PROPERTY";
    public static final String COMPOSITION_RULE_HEADER = "=== COMPOSITION_RULE";
    public static final String COMPONENT = "COMPONENT";
    public static final String UNDEFINED = "UNDEFINED";
    public static final String ASSUMPTION = "ASSUMPTION";
    public static final String COMMENT = "%";
}
