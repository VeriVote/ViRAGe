package com.fr2501.virage.jobs;

import com.fr2501.virage.core.VirageUserInterface;

/**
 * A {@link VirageJob} that offers an explicit result. It might still have side effects.
 *
 */
public abstract class VirageJobWithExplicitResult<T> extends VirageJob<T> {
    /**
     * The result of this job.
     */
    protected T result;

    /**
     * Simple constructor.
     *
     * @param issuer the issuing ui
     */
    public VirageJobWithExplicitResult(final VirageUserInterface issuer) {
        super(issuer);
    }

    @Override
    public final T getResult() {
        return this.result;
    }

    /**
     * Safe to override.
     */
    @Override
    public String toString() {
        String res = super.toString();

        String resultString = "null";
        if (this.result != null) {
            resultString = this.result.toString();
        }

        res += "Result: " + resultString + System.lineSeparator();

        return res;
    }
}
