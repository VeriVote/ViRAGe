package com.fr2501.virage.test.unit;

import java.io.IOException;

import com.fr2501.virage.analyzer.AdmissionCheckPrologCompositionAnalyzer;
import com.fr2501.virage.analyzer.CompositionAnalyzer;
import com.fr2501.virage.types.ExternalSoftwareUnavailableException;

/**
 * Tests for AdmissionCheckPrologCompositionAnalyzerTest.
 *
 */
public final class AdmissionCheckPrologCompositionAnalyzerTest extends CompositionAnalyzerTest {

    @Override
    protected CompositionAnalyzer createInstance()
            throws IOException, ExternalSoftwareUnavailableException {
        return new AdmissionCheckPrologCompositionAnalyzer(this.framework);
    }
}
