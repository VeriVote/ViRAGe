package com.fr2501.virage.test.deploy;

import static org.junit.Assert.fail;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import org.junit.Test;

/**
 * Deployment test to check whether Isabelle is available.
 *
 */
public class IsabelleTest {
  private static final Logger logger = LogManager.getLogger(IsabelleTest.class);

  @Test
  public void checkIsabelleAvailability() {
    try {
      Process isabelle = Runtime.getRuntime().exec("isabelle");
      isabelle.waitFor();
    } catch (Exception e) {
      logger.error("Isabelle could not be initialized. Make sure "
          + "Isabelle is installed and available as command "
          + "(e.g. by calling \"isabelle\" via your preferred "
          + "terminal). If this does not work Isabelle is either "
          + "not installed or your system is unable to find the "
          + "corresponding executable. How to resolve the second case "
          + "depends heavily on your OS.");
      fail();
    }
  }
}
