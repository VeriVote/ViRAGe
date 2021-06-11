package com.fr2501.virage.prolog;

/**
 * Saves which part of the extended Prolog file is currently handled.
 *
 */

public enum ParserState {
  STARTING, FRAMEWORK_COMPONENT, COMPOSITION_TYPE, COMPOSABLE_MODULE, COMPOSITIONAL_STRUCTURE,
  PROPERTY, COMPOSITION_RULE,
}
