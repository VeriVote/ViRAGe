package com.fr2501.virage.isabelle;

import java.util.Map;

/**
 * An {@link IsabelleEvent} raised when a command finishes successfully, only
 * applicable for some commands. Others might raise an
 * {@link IsabelleFinishedEvent} with key-value pair ("ok"="true").
 *
 */
public class IsabelleOkEvent extends IsabelleEvent {

  public IsabelleOkEvent(Map<String, String> parameters) {
    super(parameters);
  }
}
