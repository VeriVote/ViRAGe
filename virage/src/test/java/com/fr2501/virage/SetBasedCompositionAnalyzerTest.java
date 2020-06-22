package com.fr2501.virage;

import java.util.Set;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import org.junit.Test;

import com.fr2501.util.StringUtils;
import com.fr2501.virage.analyzer.CompositionAnalyzer;
import com.fr2501.virage.analyzer.SetBasedCompositionAnalyzer;
import com.fr2501.virage.analyzer.SimplePrologCompositionAnalyzer;
import com.fr2501.virage.prolog.QueryState;
import com.fr2501.virage.types.DecompositionTree;
import com.fr2501.virage.types.Property;
import com.fr2501.virage.types.SearchResult;
import com.fr2501.virage.types.ValueNotPresentException;

public class SetBasedCompositionAnalyzerTest extends CompositionAnalyzerTest {
	private static final Logger logger = LogManager.getLogger(SetBasedCompositionAnalyzer.class);
	
	protected CompositionAnalyzer createInstance() {
		return new SetBasedCompositionAnalyzer(this.framework);
	}
	
	@Test
	public void testAccordanceWithSPCA() throws ValueNotPresentException {
		SimplePrologCompositionAnalyzer spca = new SimplePrologCompositionAnalyzer(this.framework);
		SetBasedCompositionAnalyzer sbca = new SetBasedCompositionAnalyzer(this.framework);
		
		final int RUNS = 100;
		final int TIMEOUT = 10;
		
		spca.setTimeout(TIMEOUT);
		sbca.setTimeout(TIMEOUT);
		
		int conflicts = 0;
		int errors = 0;
		
		for(int i=0; i<RUNS; i++) {
			int amount = (int) (5 * Math.random()) + 1;
			
			Set<Property> properties = this.generator.getRandomComposableModuleProperties(amount);
			
			logger.info(StringUtils.printCollection(properties));
			
			SearchResult<DecompositionTree> trustedResult = spca.generateComposition(properties);
			SearchResult<DecompositionTree> result = sbca.generateComposition(properties);
			
			if(result.getState() == QueryState.ERROR) {
				errors++;
			}
			
			if(trustedResult.getState() == QueryState.FAILED) {
				if(result.getState() == QueryState.SUCCESS) {
					conflicts++;
				}
			}
			
			if(trustedResult.getState() == QueryState.SUCCESS) {
				if(result.getState() == QueryState.FAILED) {
					conflicts++;
				}
			}
		}
		
		if(errors > 0 || conflicts > 0) {
			logger.info("Errors: " + errors);
			logger.info("Conflicts: " + conflicts);
		}
	}
}
