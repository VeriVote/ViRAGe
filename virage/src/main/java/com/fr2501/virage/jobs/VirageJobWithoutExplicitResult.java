package com.fr2501.virage.jobs;

import com.fr2501.virage.core.VirageUserInterface;

/**
 * A {@link VirageJob} without explicit result, only influences the system via side effects.
 *
 * @author VeriVote
 */
public abstract class VirageJobWithoutExplicitResult extends VirageJob<Void> {
    /**
     * Simple constructor.
     *
     * @param issuer the issuing ui.
     */
    public VirageJobWithoutExplicitResult(final VirageUserInterface issuer) {
        super(issuer);
    }

    @Override
    public final Void getResult() {
        throw new UnsupportedOperationException();
    }
}
