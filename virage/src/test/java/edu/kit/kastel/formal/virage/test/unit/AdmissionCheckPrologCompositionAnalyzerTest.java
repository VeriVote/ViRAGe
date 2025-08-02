package edu.kit.kastel.formal.virage.test.unit;

import java.io.IOException;

import edu.kit.kastel.formal.virage.analyzer.AdmissionCheckPrologCompositionAnalyzer;
import edu.kit.kastel.formal.virage.analyzer.CompositionAnalyzer;
import edu.kit.kastel.formal.virage.types.ExternalSoftwareUnavailableException;

/**
 * Tests for AdmissionCheckPrologCompositionAnalyzerTest.
 *
 * @author VeriVote
 */
public final class AdmissionCheckPrologCompositionAnalyzerTest extends CompositionAnalyzerTest {

    @Override
    protected CompositionAnalyzer createInstance()
            throws IOException, ExternalSoftwareUnavailableException {
        return new AdmissionCheckPrologCompositionAnalyzer(this.getFramework());
    }
}
