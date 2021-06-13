package com.fr2501.virage.test.deploy;

import static org.junit.Assert.fail;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import org.jpl7.JPL;
import org.junit.Test;

/**
 * Deployment test to check JPL availability.
 *
 */
public class Jpl7Test {
  private static final Logger logger = LogManager.getLogger(Jpl7Test.class);

  @Test
  public void checkJplAvailability() {
    try {
      Class.forName("org.jpl7.JPL", false, this.getClass().getClassLoader());

      String referenceVersion = "7.6.1-stable";
      String version = JPL.version_string();

      if (!version.equals(referenceVersion)) {
        logger.warn("You are using JPL version " + version + ". "
            + "ViRAGe was developed and tested using JPL version " + referenceVersion
            + ". If the program seems to behave "
            + "weirdly when running Prolog commands, consider " + "switching to that version.");
      }

    } catch (ClassNotFoundException e) {
      logger.error("JPL7 could not be located. Please " + "check whether it is set up correctly, "
          + "according to the ViRAGe ReadMe and the " + "instructions given on jpl7.org.");
      fail();
    }
  }
}
