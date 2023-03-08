package edu.kit.kastel.formal.virage.isabelle;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.nio.charset.StandardCharsets;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import edu.kit.kastel.formal.util.StringUtils;

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
                new InputStreamReader(this.isabelleClient.getInputStream(),
                                      StandardCharsets.UTF_8));
        this.stderrReader = new BufferedReader(
                new InputStreamReader(this.isabelleClient.getErrorStream(),
                                      StandardCharsets.UTF_8));

        final Thread thread = new Thread(this, "Isabelle Console Output");
        thread.start();
    }

    /**
     * Logs a sanitized message with the {@link Level#DEBUG org.apache.logging.log4j.Level.DEBUG}
     * level.
     * @param message the message string to log
     */
    private static void logSanitizedDebugMessage(final String message) {
        LOGGER.debug(StringUtils.stripAndEscape(message));
    }

    /**
     * Logs a sanitized message with the {@link Level#ERROR org.apache.logging.log4j.Level.ERROR}
     * level.
     * @param message the message string to log
     */
    private static void logSanitizedErrorMessage(final String message) {
        LOGGER.error(StringUtils.stripAndEscape(message));
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
                    logSanitizedDebugMessage(line);

                    this.handleEvent(line);
                } else if (this.stderrReader.ready()) {
                    logSanitizedErrorMessage(this.stderrReader.readLine());
                }
            } catch (final IOException e) {
                LOGGER.error("Something went wrong.", e);
                e.printStackTrace();
            }
        }
    }
}
