package com.fr2501.virage.test.unit;

import com.fr2501.virage.analyzer.CompositionAnalyzer;

import java.io.IOException;

import com.fr2501.virage.analyzer.AdmissionCheckPrologCompositionAnalyzer;

public class AdmissionCheckPrologCompositionAnalyzerTest extends CompositionAnalyzerTest {
  protected CompositionAnalyzer createInstance() throws IOException {
    return new AdmissionCheckPrologCompositionAnalyzer(this.framework);
  }
}
