package edu.kit.kastel.formal.virage.jobs;

import edu.kit.kastel.formal.virage.core.VirageUserInterface;

/**
 * A {@link VirageJob} without explicit result, only influences the system via side effects.
 *
 * @author VeriVote
 */
public abstract class VirageJobWithoutExplicitResult extends VirageJob<Void> {
    /**
     * Simple constructor.
     *
     * @param issuer the issuing user interface
     */
    public VirageJobWithoutExplicitResult(final VirageUserInterface issuer) {
        super(issuer);
    }

    @Override
    public final Void getResult() {
        throw new UnsupportedOperationException();
    }
}
