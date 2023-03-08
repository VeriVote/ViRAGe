package edu.kit.kastel.formal.virage.test.unit;

import java.io.IOException;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import edu.kit.kastel.formal.virage.analyzer.CompositionAnalyzer;
import edu.kit.kastel.formal.virage.analyzer.SimplePrologCompositionAnalyzer;
import edu.kit.kastel.formal.virage.types.ExternalSoftwareUnavailableException;
import edu.kit.kastel.formal.virage.types.ValueNotPresentException;

/**
 * Tests suite for {@link SimplePrologCompositionAnalyzer}.
 *
 * @author VeriVote
 */
public final class SimplePrologCompositionAnalyzerTest extends CompositionAnalyzerTest {
    /**
     * The logger.
     */
    private static final Logger LOGGER = LogManager
            .getLogger(SimplePrologCompositionAnalyzer.class);

    @Override
    protected CompositionAnalyzer createInstance()
            throws IOException, ExternalSoftwareUnavailableException {
        return new SimplePrologCompositionAnalyzer(this.getFramework());
    }

    // Obviously, there is nothing to be done here.
    @Override
    public void testAccordanceWithSpca() throws ValueNotPresentException {
        LOGGER.info("testAccordanceWithSPCA()");
        return;
    }
}
