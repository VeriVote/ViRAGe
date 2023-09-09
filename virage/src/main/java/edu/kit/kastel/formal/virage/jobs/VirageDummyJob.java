package edu.kit.kastel.formal.virage.jobs;

import edu.kit.kastel.formal.util.StringUtils;
import edu.kit.kastel.formal.virage.core.VirageUserInterface;

/**
 * A {@link VirageJob} that does nothing, can be used if something goes wrong while creating the
 * actual job, but a return value is still required.
 *
 * @author VeriVote
 */
public final class VirageDummyJob extends VirageJobWithoutExplicitResult {
    /**
     * Simple constructor.
     * @param issuer the issuing UI.
     */
    public VirageDummyJob(final VirageUserInterface issuer) {
        super(issuer);
    }

    @Override
    protected void concreteExecute() throws Exception {
        // skip operation
    }

    @Override
    public boolean externalSoftwareAvailable() {
        return true;
    }

    @Override
    public String getDescription() {
        return StringUtils.EMPTY;
    }

    @Override
    public String presentConcreteResult() {
        return StringUtils.EMPTY;
    }

    @Override
    public String presentResult() {
        return StringUtils.EMPTY;
    }
}
