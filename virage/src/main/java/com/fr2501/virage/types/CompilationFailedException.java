package com.fr2501.virage.types;

/**
 * An exception thrown if compilation of generated code fails.
 *
 */
public class CompilationFailedException extends Exception {
  private String message;

  /**
   * The UID.
   */
  private static final long serialVersionUID = -3356300070323059173L;

  public CompilationFailedException(String msg) {
    this.message = msg;
  }

  @Override
  public String getMessage() {
    return this.message;
  }

  @Override
  public String getLocalizedMessage() {
    return this.message;
  }

}
