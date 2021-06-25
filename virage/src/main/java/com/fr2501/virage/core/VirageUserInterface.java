package com.fr2501.virage.core;

import com.fr2501.virage.jobs.VirageJob;

/**
 * Interface specifying requirements for all user interfaces of ViRAGe.
 *
 */
public interface VirageUserInterface extends Runnable {
  /**
   * Similar to run(), but invokes its own {@link Thread} object and starts it.
   */
  public void launch();

  /**
   * Used by {@link VirageJob} objects to notify the interface of changes in their
   * state.

   * @param job the notifying job
   */
  public void notify(VirageJob<?> job);
  
  public boolean requestConfirmation(String message);
  
  public String requestString(String message);
  
  public void displayMessage(String message);
  
  public void displayError(String message);
}
