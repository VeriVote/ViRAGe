package com.fr2501.virage.jobs;

import com.fr2501.virage.core.VirageUserInterface;

/**
 * 
 * A {@link VirageJob} used to terminate the system-
 *
 */
public class VirageExitJob extends VirageJobWithoutExplicitResult {
  private int statusCode;

  public VirageExitJob(VirageUserInterface issuer, int statusCode) {
    super(issuer);

    this.statusCode = statusCode;
  }

  @Override
  public void concreteExecute() {
    this.executingCore.destroy(this.statusCode);
  }
}
