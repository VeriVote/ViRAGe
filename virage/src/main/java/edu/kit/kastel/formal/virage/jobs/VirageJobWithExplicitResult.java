package edu.kit.kastel.formal.virage.jobs;

import edu.kit.kastel.formal.virage.core.VirageUserInterface;

/**
 * A {@link VirageJob} that offers an explicit result. It might still have side effects.
 *
 * @author VeriVote
 *
 * @param <T> the type of the result
 */
public abstract class VirageJobWithExplicitResult<T> extends VirageJob<T> {
    /**
     * The result of this job.
     */
    private T result;

    /**
     * Simple constructor.
     *
     * @param issuer the issuing user interface
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

    /**
     * Simple setter.
     * @param newResult the result to set
     */
    protected void setResult(final T newResult) {
        this.result = newResult;
    }
}
