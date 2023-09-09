package edu.kit.kastel.formal.virage.test.unit;

import static org.junit.Assert.assertTrue;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.IOException;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import org.junit.Test;

import edu.kit.kastel.formal.util.SystemUtils;
import edu.kit.kastel.formal.virage.prolog.ExtendedPrologParser;
import edu.kit.kastel.formal.virage.prolog.MalformedEplFileException;
import edu.kit.kastel.formal.virage.prolog.PrologParser;
import edu.kit.kastel.formal.virage.prolog.SimpleExtendedPrologParser;
import edu.kit.kastel.formal.virage.types.FrameworkRepresentation;

/**
 * Test suite for {@link ExtendedPrologParser}.
 *
 * @author VeriVote
 */
public class ExtendedPrologParserTest {
    /**
     * The logger.
     */
    private static final Logger LOGGER = LogManager.getLogger(ExtendedPrologParserTest.class);

    /**
     * Tests loading a non-existing file.
     *
     * @throws IOException if input or output fails
     * @throws MalformedEplFileException if the file is not valid (E)PL
     */
    @Test(expected = FileNotFoundException.class)
    public void loadNonExistingFile() throws IOException, MalformedEplFileException {
        LOGGER.info("loadNonExistingFile()");
        final ExtendedPrologParser parser = new SimpleExtendedPrologParser();
        parser.parseFramework(new File(""), false);
    }

    /**
     * Tests loading an invalid (E)PL file.
     *
     * @throws IOException if input or output fails
     * @throws MalformedEplFileException if the file is not valid (E)PL
     */
    @Test(expected = MalformedEplFileException.class)
    public void loadInvalidFile() throws IOException, MalformedEplFileException {
        LOGGER.info("loadInvalidFile()");
        final ExtendedPrologParser parser = new SimpleExtendedPrologParser();
        parser.parseFramework(
                new File(SystemUtils.RESOURCES + "invalid_test" + PrologParser.DOT_PL),
                false);
    }

    /**
     * Tests the loading process of a valid EPL file.
     * <b> Note: </b> This test now depends heavily depends on the configuration file, so it is no
     * longer meaningful.
     *
     * @throws IOException if file interaction fails
     * @throws MalformedEplFileException if the file violates the EPL format
     */
    public void loadValidFile() throws IOException, MalformedEplFileException {
        LOGGER.info("loadValidFile()");
        final ExtendedPrologParser parser = new SimpleExtendedPrologParser();
        final FrameworkRepresentation framework =
                parser.parseFramework(
                        new File(SystemUtils.RESOURCES + "valid_test" + PrologParser.DOT_PL),
                        false);

        final int componentCount = 3;
        final int propertyCount = 3;
        final int compositionRuleCount = 4;

        // The first assertion now depends on a configuration file.
        // assertTrue(framework.getComponentTypes().size() == 3);
        assertTrue(framework.getComponents().size() == componentCount);
        // assertTrue(framework.getComposableModules().size() == 0);
        assertTrue(framework.getProperties().size() == propertyCount);
        assertTrue(framework.getCompositionRules().size() == compositionRuleCount);
    }

    /**
     * Tests loading a valid file.
     *
     * @throws IOException if input or output fails
     * @throws MalformedEplFileException if the file is not valid (E)PL
     */
    @Test
    public void loadFrameworkFile() throws IOException, MalformedEplFileException {
        LOGGER.info("loadFrameworkFile()");
        final ExtendedPrologParser parser = new SimpleExtendedPrologParser();
        final FrameworkRepresentation framework =
                parser.parseFramework(
                        new File(SystemUtils.RESOURCES + "framework" + PrologParser.DOT_PL),
                        false);
        LOGGER.debug(framework.toString());
    }
}
