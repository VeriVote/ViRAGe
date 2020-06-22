package com.fr2501.virage;

import com.fr2501.virage.analyzer.CompositionAnalyzer;
import com.fr2501.virage.analyzer.SimplePrologCompositionAnalyzer;

public class SimplePrologCompositionAnalyzerTest extends CompositionAnalyzerTest {
	protected CompositionAnalyzer createInstance() {
		return new SimplePrologCompositionAnalyzer(this.framework);
	}
}
