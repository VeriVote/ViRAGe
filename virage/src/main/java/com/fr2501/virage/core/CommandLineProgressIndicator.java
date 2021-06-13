package com.fr2501.virage.core;

/**
 * A simple spinning bar to indicate progress on command line interfaces.
 *
 */
public class CommandLineProgressIndicator extends ProgressIndicator {
  private int phase;
  private boolean hidden;

  protected CommandLineProgressIndicator() {
    this.phase = 0;
    this.hidden = false;
  }

  /**
   * Moves the indicator to its next state.
   */
  public void advance() {
    String message = "";
    switch (this.phase) {
      case 0:
        message = "|";
        break;
      case 1:
        message = "/";
        break;
      case 2:
        message = "-";
        break;
      case 3:
        message = "\\";
        break;
      default: break;
    }

    phase++;
    if (phase == 4) {
      phase = 0;
    }

    if (!this.hidden) {
      System.out.print(message + "\r");
    }
  }

  public void hide() {
    System.out.println("");
    this.hidden = true;
  }

  public void show() {
    this.hidden = false;
  }
}
