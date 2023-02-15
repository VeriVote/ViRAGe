package com.fr2501.util;

/**
 * A simple mutex mechanism.
 *
 * @author VeriVote
 */
public class ThreadSignal {
    /**
     * True if finished, false otherwise.
     */
    private boolean finished;

    private synchronized boolean getFinished() {
        return this.finished;
    }

    /**
     * Set signal to finished.
     */
    public synchronized void finish() {
        this.finished = true;
    }

    /**
     * A blocking function that returns when this.finished is true.
     */
    public void waitFor() {
        while (true) {
            synchronized (this) {
                if (this.getFinished()) {
                    return;
                }
            }
        }
    }
}
