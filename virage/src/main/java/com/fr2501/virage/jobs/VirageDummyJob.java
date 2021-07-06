package com.fr2501.virage.jobs;

import com.fr2501.virage.core.VirageUserInterface;

/**
 * A {@link VirageJob} that does nothing, can be used if something goes wrong while creating the
 * actual job, but a return value is still required.
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

    @Override
    public String presentResult() {
        return "";
    }

    @Override
    public String presentConcreteResult() {
        return "";
    }

    @Override
    public String getDescription() {
        return "";
    }

}
