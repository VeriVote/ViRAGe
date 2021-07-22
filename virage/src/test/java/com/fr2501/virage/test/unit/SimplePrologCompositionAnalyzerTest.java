package com.fr2501.virage.test.unit;

import java.io.IOException;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import com.fr2501.virage.analyzer.CompositionAnalyzer;
import com.fr2501.virage.analyzer.SimplePrologCompositionAnalyzer;
import com.fr2501.virage.types.ExternalSoftwareUnavailableException;
import com.fr2501.virage.types.ValueNotPresentException;

/**
 * Tests suite for {@link SimplePrologCompositionAnalyzer}.
 *
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
        return new SimplePrologCompositionAnalyzer(this.framework);
    }

    // Obviously, there is nothing to be done here.
    @Override
    public void testAccordanceWithSpca() throws ValueNotPresentException {
        LOGGER.info("testAccordanceWithSPCA()");
        return;
    }
}
