package com.fr2501.virage.jobs;

import java.time.Instant;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import com.fr2501.util.ProgressIndicator;
import com.fr2501.virage.core.VirageCore;
import com.fr2501.virage.core.VirageUserInterface;

/**
 * 
 * Wrapper class for all tasks to be completed by
 * {@link com.fr2501.virage.core.VirageCore}. Require a
 * {@link VirageUserInterface} as listener.
 *
 * @param <T> the result type
 */
public abstract class VirageJob<T> {
  protected static final Logger logger = LogManager.getLogger(VirageJob.class);
  private VirageUserInterface issuer;

  protected VirageCore executingCore;
  protected VirageJobState state;

  private static long next_id = 0;

  private long id;

  private long time_issued;
  private long time_started;
  private long time_finished;

  int phase = 0;

  public VirageJob(VirageUserInterface issuer) {
    this.issuer = issuer;
    this.id = VirageJob.next_id;
    VirageJob.next_id++;

    this.time_issued = System.currentTimeMillis();

    this.state = VirageJobState.PENDING;
  }

  /**
   * Runs the job and notifies its issuer on termination. Should only be ran after
   * checking isReadyToExecute(), otherwise behaviour is undefined.
   * 
   * @param core the executing core
   */
  public void execute(VirageCore core) {
    this.executingCore = core;
    this.setState(VirageJobState.RUNNING);

    try {
      this.concreteExecute();
      this.setState(VirageJobState.FINISHED);
    } catch (Exception e) {
      logger.error("An error occured.", e);
      this.setState(VirageJobState.FAILED);
    }

    this.issuer.notify(this);
  }
  
  public abstract boolean externalSoftwareAvailable();

  /**
   * The actual implementation of the job's functionality
   * 
   * @throws Exception which will be caught by the
   *                   {@link com.fr2501.virage.core.VirageCore} object
   */
  protected abstract void concreteExecute() throws Exception;

  public abstract T getResult();

  public synchronized VirageJobState getState() {
    return this.state;
  }

  /**
   * Sets the current state, also updates the timestamps if applicable.
   * 
   * @param state the new state
   */
  public void setState(VirageJobState state) {
    if (state == VirageJobState.RUNNING) {
      this.time_started = System.currentTimeMillis();
    } else if (state == VirageJobState.FAILED || state == VirageJobState.FINISHED) {
      this.time_finished = System.currentTimeMillis();
    }

    this.state = state;
  }

  /**
   * Halts execution until this is finished ({@link VirageJobState#FINISHED} or
   * {@link VirageJobState#FAILED})
   */
  public void waitFor() {
    ProgressIndicator progressIndicator = new ProgressIndicator();
    
    while (true) {
      boolean finished = false;
      synchronized (this) {
        finished = (this.getState() != VirageJobState.PENDING && this.getState() != VirageJobState.RUNNING);
      }

      if (finished)
        return;
     
      try {
        Thread.sleep(250);
      } catch (InterruptedException e) {
        // TODO Auto-generated catch block
        e.printStackTrace();
      }
      
      progressIndicator.advance();
    }
  }

  @Override
  public String toString() {
    String res = "----------- " + this.getClass().getCanonicalName() + "\n";
    res += "ID: " + this.id + "\n";

    res += "Issued: " + Instant.ofEpochMilli(time_issued).toString() + "\n";
    res += "Started: " + Instant.ofEpochMilli(time_started).toString() + "\n";
    res += "Finished: " + Instant.ofEpochMilli(time_finished).toString() + "\n";
    res += "Time elapsed: " + (time_finished - time_started) + " milliseconds \n";
    res += "-----\n";
    res += "State: " + this.state + "\n";

    return res;
  }
}
