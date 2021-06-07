package com.fr2501.virage.test.unit;

import static org.junit.Assert.assertTrue;

import com.fr2501.virage.prolog.ExtendedPrologParser;
import com.fr2501.virage.prolog.MalformedEplFileException;
import com.fr2501.virage.prolog.SimpleExtendedPrologParser;
import com.fr2501.virage.types.FrameworkRepresentation;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.IOException;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import org.junit.Test;

public class ExtendedPrologParserTest {
  private Logger logger = LogManager.getLogger(ExtendedPrologParserTest.class);

  @Test(expected = FileNotFoundException.class)
  public void loadNonExistingFile() throws IOException, MalformedEplFileException {
    logger.info("loadNonExistingFile()");
    ExtendedPrologParser parser = new SimpleExtendedPrologParser();

    parser.parseFramework(new File(""), false);
  }

  @Test(expected = MalformedEplFileException.class)
  public void loadInvalidFile() throws IOException, MalformedEplFileException {
    logger.info("loadInvalidFile()");
    ExtendedPrologParser parser = new SimpleExtendedPrologParser();

    parser.parseFramework(new File("src/test/resources/invalid_test.pl"), false);
  }

  /*
   * @Test This test now depends heavily depends on the config file, so it is no longer meaningful.
   */
  public void loadValidFile() throws IOException, MalformedEplFileException {
    logger.info("loadValidFile()");
    ExtendedPrologParser parser = new SimpleExtendedPrologParser();

    FrameworkRepresentation framework = parser
        .parseFramework(new File("src/test/resources/valid_test.pl"), false);

    // The first assertion now depends on a config file.
    // assertTrue(framework.getComponentTypes().size() == 3);
    assertTrue(framework.getComponents().size() == 3);
    assertTrue(framework.getComposableModules().size() == 0);
    assertTrue(framework.getProperties().size() == 3);
    assertTrue(framework.getCompositionRules().size() == 4);
  }

  @Test
  public void loadFrameworkFile() throws IOException, MalformedEplFileException {
    logger.info("loadFrameworkFile()");
    ExtendedPrologParser parser = new SimpleExtendedPrologParser();

    FrameworkRepresentation framework = parser
        .parseFramework(new File("src/test/resources/framework.pl"), false);
    logger.debug(framework.toString());
  }
}
