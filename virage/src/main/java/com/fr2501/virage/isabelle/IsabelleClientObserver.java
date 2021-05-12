package com.fr2501.virage.isabelle;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

/**
 * 
 * Observes an Isabelle client process and creates {@link IsabelleEvent}s if
 * necessary.
 *
 */
public class IsabelleClientObserver implements Runnable {
  private static final Logger logger = LogManager.getLogger(IsabelleClientObserver.class);
  private IsabelleProofChecker listener;

  private Process isabelleClient;
  private IsabelleEventFactory factory;

  private BufferedReader stdoutReader;
  private BufferedReader stderrReader;

  private IsabelleClientObserver(IsabelleProofChecker listener, Process isabelleClient) {
    this.listener = listener;
    this.isabelleClient = isabelleClient;
    this.factory = new IsabelleEventFactory();

    this.stdoutReader = new BufferedReader(new InputStreamReader(this.isabelleClient.getInputStream()));
    this.stderrReader = new BufferedReader(new InputStreamReader(this.isabelleClient.getErrorStream()));

    Thread thread = new Thread(this, "isa_obs");
    thread.start();
  }

  /**
   * Starts a new IsabelleClientObserver. This is done because the object
   * reference is not really required within the calling application code.
   * 
   * @param listener       the {@link IsabelleProofChecker} to be notified on
   *                       events
   * @param isabelleClient the Isabelle client process to be watched
   */
  public static void start(IsabelleProofChecker listener, Process isabelleClient) {
    new IsabelleClientObserver(listener, isabelleClient);
  }

  @Override
  public synchronized void run() {
    while (true) {
      try {
        if (this.stdoutReader.ready()) {
          String line = this.stdoutReader.readLine();
          logger.debug(line);

          this.handleEvent(line);
        } else if (this.stderrReader.ready()) {
          logger.error(this.stderrReader.readLine());
        }
      } catch (IOException e) {
        logger.error("Something went wrong.", e);
        e.printStackTrace();
      }
    }
  }

  private synchronized void handleEvent(String s) {
    this.listener.notify(this.factory.createEvent(s));
  }
}
