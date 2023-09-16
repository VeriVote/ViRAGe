package edu.kit.kastel.formal.virage.jobs;

import java.io.IOException;

import edu.kit.kastel.formal.util.StringUtils;
import edu.kit.kastel.formal.util.SystemUtils;
import edu.kit.kastel.formal.virage.core.VirageCore;
import edu.kit.kastel.formal.virage.core.VirageUserInterface;
import edu.kit.kastel.formal.virage.prolog.MalformedEplFileException;
import edu.kit.kastel.formal.virage.types.CodeGenerationFailedException;
import edu.kit.kastel.formal.virage.types.FrameworkExtractionFailedException;

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

    private static String printPropertyLine(final String... args) {
        return StringUtils.printCollection2(args) + System.lineSeparator();
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
        } catch (final IOException | InterruptedException | FrameworkExtractionFailedException
                    | CodeGenerationFailedException | MalformedEplFileException e) {
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
        res += StringUtils.sentence(
                StringUtils.printCollection2("Started at", SystemUtils.getTime(this.timeStarted)));
        res += StringUtils.sentence(
                StringUtils.printCollection2(
                        "Job ran for",
                        SystemUtils.getDuration(this.timeStarted, this.timeFinished)));
        if (this.state == VirageJobState.FINISHED) {
            res += this.presentConcreteResult() + System.lineSeparator();
        } else {
            res += StringUtils.sentence("Something went wrong while executing this job");
        }
        res += StringUtils.repeat(StringUtils.TEN, StringUtils.DASH);
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
        final boolean started = this.state != VirageJobState.PENDING;
        final long lastMeasurement = finished ? this.timeFinished : System.currentTimeMillis();
        final String dashLine = StringUtils.repeat(11, StringUtils.DASH);

        final String issueTime = SystemUtils.getTime(this.timeIssued);
        final String startTime = started ? SystemUtils.getTime(this.timeStarted) : "not yet";
        final String elapsedTime =
                started ? SystemUtils.getDuration(this.timeStarted, lastMeasurement) : "none";
        final String finishedString = finished ? "Finished:" : "Now:";

        String res = printPropertyLine(dashLine, this.getClass().getCanonicalName());
        res += printPropertyLine("ID:", Long.toString(this.id));
        res += printPropertyLine("Issued:", issueTime);
        res += printPropertyLine("Started:", startTime);
        res += printPropertyLine(finishedString, SystemUtils.getTime(lastMeasurement));
        res += printPropertyLine("Elapsed time:", elapsedTime);
        res += printPropertyLine(StringUtils.repeat(StringUtils.FIVE, StringUtils.DASH));
        res += printPropertyLine("State:", this.state.toString());
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
     * @throws IOException                        if reading a file or other file system
     *                                            interaction fails
     * @throws InterruptedException               if execution is interrupted by the OS
     * @throws FrameworkExtractionFailedException if extracting the framework failed, possibly due
     *                                            to missing or incorrect dependencies
     * @throws CodeGenerationFailedException      in case of input, output or interruption failures
     *                                            in case of file operation failure or similar
     *                                            compilation of generated code fails
     * @throws MalformedEplFileException          if the input does not follow the specification
     *                                            of the extended Prolog format
     */
    protected abstract void concreteExecute()
            throws IOException, InterruptedException, FrameworkExtractionFailedException,
                   CodeGenerationFailedException, MalformedEplFileException;

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
