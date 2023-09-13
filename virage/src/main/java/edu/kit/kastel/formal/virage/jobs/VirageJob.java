package edu.kit.kastel.formal.virage.jobs;

import edu.kit.kastel.formal.util.StringUtils;
import edu.kit.kastel.formal.util.SystemUtils;
import edu.kit.kastel.formal.virage.core.VirageCore;
import edu.kit.kastel.formal.virage.core.VirageUserInterface;

/**
 * Wrapper class for all tasks to be completed by
 * {@link edu.kit.kastel.formal.virage.core.VirageCore}.
 * Requires a {@link VirageUserInterface} as listener.
 *
 * @author VeriVote
 * @param <T> the result type
 */
public abstract class VirageJob<T> {
    /**
     * The next available ID for a new job.
     */
    private static long nextID;

    /**
     * The core object executing this job.
     */
    private VirageCore executingCore;

    /**
     * The current state of this job.
     */
    private VirageJobState state;

    /**
     * The issuing user interface.
     */
    private final VirageUserInterface issuer;

    /**
     * The ID of this job.
     */
    private final long id;

    /**
     * Time when this job was accepted by a core.
     */
    private final long timeIssued;

    /**
     * Starting time of this job.
     */
    private long timeStarted;

    /**
     * Finishing time of this job.
     */
    private long timeFinished;

    /**
     * Simple constructor.
     *
     * @param issuerValue the issuing user interface
     */
    public VirageJob(final VirageUserInterface issuerValue) {
        this.issuer = issuerValue;
        this.id = VirageJob.nextID;
        incrementNextID();
        this.timeIssued = System.currentTimeMillis();
        this.state = VirageJobState.PENDING;
    }

    private static synchronized void incrementNextID() {
        nextID++;
    }

    /**
     * Runs the job and notifies its issuer on termination. Should only be run after checking
     * {@link #externalSoftwareAvailable()}, otherwise behavior is undefined.
     *
     * @param core the executing core
     */
    public void execute(final VirageCore core) {
        this.executingCore = core;
        this.setState(VirageJobState.RUNNING);
        try {
            this.concreteExecute();
            this.setState(VirageJobState.FINISHED);
            // this.concreteExecute() can throw virtually any runtime exception.
        } catch (final Exception e) {
            e.printStackTrace();
            this.setState(VirageJobState.FAILED);
        }
    }

    /**
     * Checks whether all required external dependencies are satisfied.
     *
     * @return true if they are, false otherwise
     */
    public abstract boolean externalSoftwareAvailable();

    /**
     * Returns a description of the job's task.
     *
     * @return the description
     */
    public abstract String getDescription();

    /**
     * Returns the result of this job if one is available.
     *
     * @return the result
     */
    public abstract T getResult();

    /**
     * Returns the current {@link VirageJobState} state of the ViRAGe job.
     *
     * @return the {@link VirageJobState}
     */
    public final synchronized VirageJobState getState() {
        return this.state;
    }

    /**
     * Pretty-printed result of this job.
     *
     * @return a pretty-printed String
     */
    public abstract String presentConcreteResult();

    /**
     * Pretty-print job, safe to override.
     *
     * @return a pretty-printed String representation of this job
     */
    public String presentResult() {
        String res = StringUtils.EMPTY;
        res += StringUtils.sentence(StringUtils.addSpace("Started at")
                                    + SystemUtils.getTime(this.timeStarted));
        res += StringUtils.sentence(StringUtils.addSpace("Job ran for")
                + SystemUtils.getDuration(this.timeStarted, this.timeFinished));
        if (this.state == VirageJobState.FINISHED) {
            res += this.presentConcreteResult() + System.lineSeparator();
        } else {
            res += StringUtils.sentence("Something went wrong while executing this job");
        }
        res += "----------";
        return res;
    }

    /**
     * Sets the current state, also updates the time stamps if applicable.
     *
     * @param newState the new state
     */
    public void setState(final VirageJobState newState) {
        this.state = newState;
        if (newState == VirageJobState.RUNNING) {
            this.timeStarted = System.currentTimeMillis();
        } else if (newState == VirageJobState.FAILED || newState == VirageJobState.FINISHED) {
            this.timeFinished = System.currentTimeMillis();
            this.issuer.notify(this);
        }
    }

    /**
     * Safe to override.
     */
    @Override
    public String toString() {
        final boolean finished =
                this.state == VirageJobState.FAILED || this.state == VirageJobState.FINISHED;
        final long lastMeasurement = finished ? this.timeFinished : System.currentTimeMillis();
        String res = StringUtils.addSpace("-----------") + this.getClass().getCanonicalName()
                        + System.lineSeparator();
        res += StringUtils.addSpace("ID:") + this.id + System.lineSeparator();
        res += StringUtils.addSpace("Issued:")
                + SystemUtils.getTime(this.timeIssued) + System.lineSeparator();
        res += StringUtils.addSpace("Started:")
                + SystemUtils.getTime(this.timeStarted) + System.lineSeparator();
        res += (finished ? StringUtils.addSpace("Finished:") : StringUtils.addSpace("Now:"))
                + SystemUtils.getTime(lastMeasurement) + System.lineSeparator();
        res += StringUtils.addSpace("Elapsed time:")
                + SystemUtils.getDuration(this.timeStarted, lastMeasurement)
                + System.lineSeparator();
        res += "-----" + System.lineSeparator();
        res += StringUtils.addSpace("State:") + this.state + System.lineSeparator();
        return res;
    }

    /**
     * Halts execution until this is finished ({@link VirageJobState#FINISHED} or
     * {@link VirageJobState#FAILED}).
     */
    public void waitFor() {
        while (true) {
            boolean finished = false;
            synchronized (this) {
                finished = this.getState() != VirageJobState.PENDING
                        && this.getState() != VirageJobState.RUNNING;
            }
            if (finished) {
                return;
            }
            SystemUtils.semiBusyWaitingHelper();
        }
    }

    /**
     * The actual implementation of the job's functionality.
     *
     * @throws Exception which will be caught by the
     *     {@link edu.kit.kastel.formal.virage.core.VirageCore} object
     */
    protected abstract void concreteExecute() throws Exception;

    /**
     * Simple getter.
     *
     * @return the executingCore
     */
    protected VirageCore getExecutingCore() {
        return this.executingCore;
    }

    /**
     * Simple setter.
     *
     * @param executingCoreValue the executingCore to set
     */
    protected void setExecutingCore(final VirageCore executingCoreValue) {
        this.executingCore = executingCoreValue;
    }
}
