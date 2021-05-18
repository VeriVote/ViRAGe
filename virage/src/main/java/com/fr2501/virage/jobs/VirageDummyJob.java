package com.fr2501.virage.jobs;

import com.fr2501.virage.core.VirageUserInterface;

/**
 * 
 * A {@link VirageJob} that does nothing, can be used if something goes wrong
 * while creating the actual job, but something still has to be returned.
 *
 */
public class VirageDummyJob extends VirageJobWithoutExplicitResult {

  public VirageDummyJob(VirageUserInterface issuer) {
    super(issuer);
  }

  @Override
  protected void concreteExecute() throws Exception {
    // no-op
  }

  @Override
  public boolean externalSoftwareAvailable() {
    return true;
  }

}
