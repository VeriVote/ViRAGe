package com.fr2501.virage.jobs;

import com.fr2501.virage.core.VirageUserInterface;

/**
 * 
 * A {@link VirageJob} that offers an explicit result. It might still have side
 * effects.
 *
 */
public abstract class VirageJobWithExplicitResult<T> extends VirageJob<T> {
  protected T result;

  public VirageJobWithExplicitResult(VirageUserInterface issuer) {
    super(issuer);
  }

  public T getResult() {
    return this.result;
  }

  @Override
  public String toString() {
    String res = super.toString();

    String resultString = "null";
    if (this.result != null) {
      resultString = this.result.toString();
    }

    res += "Result: " + resultString + "\n";

    return res;
  }
}
