package com.fr2501.virage.test.unit;

import com.fr2501.virage.analyzer.CompositionAnalyzer;
import com.fr2501.virage.analyzer.SimplePrologCompositionAnalyzer;
import com.fr2501.virage.types.ExternalSoftwareUnavailableException;
import com.fr2501.virage.types.ValueNotPresentException;
import java.io.IOException;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

/**
 * Tests suite for {@link SimplePrologCompositionAnalyzer}.
 *
 */
public class SimplePrologCompositionAnalyzerTest extends CompositionAnalyzerTest {
    private static final Logger logger = LogManager
            .getLogger(SimplePrologCompositionAnalyzer.class);

    protected CompositionAnalyzer createInstance()
            throws IOException, ExternalSoftwareUnavailableException {
        return new SimplePrologCompositionAnalyzer(this.framework);
    }

    // Obviously, there is nothing to be done here.
    @Override
    public void testAccordanceWithSpca() throws ValueNotPresentException {
        logger.info("testAccordanceWithSPCA()");
        return;
    }
}
