package com.fr2501.virage.jobs;

import com.fr2501.virage.core.VirageUserInterface;

/**
 * A {@link VirageJob} used to terminate the system.
 *
 * @author VeriVote
 */
public final class VirageExitJob extends VirageJobWithoutExplicitResult {
    /**
     * The exit code to be given to the OS.
     */
    private final int statusCode;

    /**
     * Simple constructor.
     *
     * @param issuer the issuer
     * @param statusCode the intended exit code
     */
    public VirageExitJob(final VirageUserInterface issuer, final int statusCode) {
        super(issuer);

        this.statusCode = statusCode;
    }

    @Override
    public void concreteExecute() {
        this.executingCore.destroy(this.statusCode);
    }

    @Override
    public boolean externalSoftwareAvailable() {
        return true;
    }

    @Override
    public String getDescription() {
        return "Terminating ...";
    }

    @Override
    public String presentConcreteResult() {
        return "Terminated with exit code " + this.statusCode + ".";
    }
}
