package com.fr2501.virage.test.unit;

import com.fr2501.virage.analyzer.AdmissionCheckPrologCompositionAnalyzer;
import com.fr2501.virage.analyzer.CompositionAnalyzer;
import com.fr2501.virage.types.ExternalSoftwareUnavailableException;
import java.io.IOException;

public class AdmissionCheckPrologCompositionAnalyzerTest extends CompositionAnalyzerTest {
  protected CompositionAnalyzer createInstance()
      throws IOException, ExternalSoftwareUnavailableException {
    return new AdmissionCheckPrologCompositionAnalyzer(this.framework);
  }
}
