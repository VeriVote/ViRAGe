package com.fr2501.virage;

import com.fr2501.virage.analyzer.CompositionAnalyzer;
import com.fr2501.virage.analyzer.SimplePrologCompositionAnalyzer;
import com.fr2501.virage.types.ValueNotPresentException;

public class SimplePrologCompositionAnalyzerTest extends CompositionAnalyzerTest {
	protected CompositionAnalyzer createInstance() {
		return new SimplePrologCompositionAnalyzer(this.framework);
	}
	
	// Obviously, there is nothing to be done here.
	@Override
	public void testAccordanceWithSPCA() throws ValueNotPresentException {
		return;
	}
}
