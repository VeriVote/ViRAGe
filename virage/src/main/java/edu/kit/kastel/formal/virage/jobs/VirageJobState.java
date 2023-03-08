package edu.kit.kastel.formal.virage.jobs;

/**
 * The different states a {@link VirageJob} can be in.
 *
 * @author VeriVote
 */
public enum VirageJobState {
    /**
     * Job is waiting for execution.
     */
    PENDING,
    /**
     * Job is currently under execution.
     */
    RUNNING,
    /**
     * Job execution failed.
     */
    FAILED,
    /**
     * Job finished without errors.
     */
    FINISHED
}
