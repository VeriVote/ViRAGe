package com.fr2501.virage.core;

import java.util.List;

import com.fr2501.virage.jobs.VirageJob;

/**
 * Interface specifying requirements for all user interfaces of ViRAGe.
 *
 * @author VeriVote
 */
public interface VirageUserInterface extends Runnable {
    /**
     * Displays a list of alternatives and lets user choose one.
     * @param message additional message
     * @param alternatives the alternatives to choose from
     * @return the index of the user's choice
     */
    int chooseAlternative(String message, List<?> alternatives);

    /**
     * Display error message.
     * @param message the message
     */
    void displayError(String message);

    /**
     * Display message.
     * @param message the message
     */
    void displayMessage(String message);

    /**
     * Similar to run(), but invokes its own {@link Thread} object and starts it.
     */
    void launch();

    /**
     * Used by {@link VirageJob} objects to notify the interface of changes in their state.
     *
     * @param job the notifying job
     */
    void notify(VirageJob<?> job);

    /**
     * Display message and request user confirmation, blocking until answer is given.
     * @param message the message
     * @return true if user answer starts with "y", false if "n".
     */
    boolean requestConfirmation(String message);

    /**
     * Displays message and requests a String from the user.
     * @param message the message
     * @return the string as given by the user
     */
    String requestString(String message);
}
