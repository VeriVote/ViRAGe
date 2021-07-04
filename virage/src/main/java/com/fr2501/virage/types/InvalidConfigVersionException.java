package com.fr2501.virage.types;

import java.io.IOException;

public class InvalidConfigVersionException extends RuntimeException {

  /**
   * 
   */
  private static final long serialVersionUID = 6116199849357596875L;

  public InvalidConfigVersionException(String message) {
    super(message);
  }
}
