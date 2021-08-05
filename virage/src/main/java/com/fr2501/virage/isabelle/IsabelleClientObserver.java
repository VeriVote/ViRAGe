package com.fr2501.virage.isabelle;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

/**
 * Observes an Isabelle client process and creates {@link IsabelleEvent}s if necessary.
 *
 * @author VeriVote
 */
public final class IsabelleClientObserver implements Runnable {
    /**
     * The logger.
     */
    private static final Logger LOGGER = LogManager.getLogger(IsabelleClientObserver.class);
    /**
     * Proof checker acting as listener.
     */
    private final IsabelleProofChecker listener;

    /**
     * The Isabelle client process.
     */
    private final Process isabelleClient;
    /**
     * The Isabelle event factory.
     */
    private final IsabelleEventFactory factory;

    /**
     * Reader for stdout.
     */
    private final BufferedReader stdoutReader;
    /**
     * Reader for stderr.
     */
    private final BufferedReader stderrReader;

    private IsabelleClientObserver(final IsabelleProofChecker listenerValue,
            final Process isabelleClientValue) {
        this.listener = listenerValue;
        this.isabelleClient = isabelleClientValue;
        this.factory = new IsabelleEventFactory();

        this.stdoutReader = new BufferedReader(
                new InputStreamReader(this.isabelleClient.getInputStream()));
        this.stderrReader = new BufferedReader(
                new InputStreamReader(this.isabelleClient.getErrorStream()));

        final Thread thread = new Thread(this, "Isabelle Console Output");
        thread.start();
    }

    /**
     * Starts a new IsabelleClientObserver. This is done because the object reference is not really
     * required within the calling application code.
     *
     * @param listener the {@link IsabelleProofChecker} to be notified on events
     * @param isabelleClient the Isabelle client process to be watched
     */
    public static void start(final IsabelleProofChecker listener, final Process isabelleClient) {
        new IsabelleClientObserver(listener, isabelleClient);
    }

    private synchronized void handleEvent(final String s) {
        this.listener.notify(this.factory.createEvent(s));
    }

    @Override
    public synchronized void run() {
        while (true) {
            try {
                if (this.stdoutReader.ready()) {
                    final String line = this.stdoutReader.readLine();
                    LOGGER.debug(line);

                    this.handleEvent(line);
                } else if (this.stderrReader.ready()) {
                    LOGGER.error(this.stderrReader.readLine());
                }
            } catch (final IOException e) {
                LOGGER.error("Something went wrong.", e);
                e.printStackTrace();
            }
        }
    }
}
