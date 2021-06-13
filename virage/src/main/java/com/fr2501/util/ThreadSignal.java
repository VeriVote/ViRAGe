package com.fr2501.util;

/**
 * A simple mutex mechanism.
 *
 */
public class ThreadSignal {
  private boolean finished = false;

  private synchronized boolean getFinished() {
    return this.finished;
  }

  public synchronized void finish() {
    this.finished = true;
  }

  /**
   * A blocking function that returns when this.finished is true.
   */
  public void waitFor() {
    while (true) {
      synchronized (this) {
        if (this.getFinished()) {
          return;
        }
      }
    }
  }
}
