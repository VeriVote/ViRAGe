package com.fr2501.virage.isabelle;

import java.util.Map;

/**
 * A class to represent the events raised by the Isabelle CLI.
 *
 */
public abstract class IsabelleEvent {
  private Map<String, String> parameters;

  public IsabelleEvent(Map<String, String> parameters) {
    this.parameters = parameters;
  }

  public String getValue(String key) {
    return this.parameters.get(key);
  }

  /**
   * Applies the effects of this event to its observer.
   * 
   * @param observer The {@link IsabelleProofChecker} observing the event
   */
  public void applyEffects(IsabelleProofChecker observer) {
    // default: no-op
  }

  @Override
  public String toString() {
    String res = this.getClass().getCanonicalName();

    for (String key : this.parameters.keySet()) {
      res += "\n\t" + key + ": " + this.parameters.get(key);
    }

    return res;
  }
}
