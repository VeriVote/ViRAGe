package com.fr2501.virage.jobs;

import com.fr2501.virage.core.VirageUserInterface;

/**
 * 
 * A {@link VirageJob} without explicit result, only influences the system via
 * side effects.
 *
 */
public abstract class VirageJobWithoutExplicitResult extends VirageJob<Void> {
  public VirageJobWithoutExplicitResult(VirageUserInterface issuer) {
    super(issuer);
  }

  @Override
  public Void getResult() {
    throw new UnsupportedOperationException();
  }
}
