package edu.kit.kastel.formal.virage.jobs;

import edu.kit.kastel.formal.util.StringUtils;
import edu.kit.kastel.formal.virage.core.VirageUserInterface;

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
     * @param statusCodeValue the intended exit code
     */
    public VirageExitJob(final VirageUserInterface issuer, final int statusCodeValue) {
        super(issuer);

        this.statusCode = statusCodeValue;
    }

    @Override
    public void concreteExecute() {
        this.getExecutingCore().destroy(this.statusCode);
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
        return "Terminated with exit code " + this.statusCode + StringUtils.PERIOD;
    }
}
