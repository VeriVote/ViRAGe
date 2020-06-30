package com.fr2501.virage;

import static org.junit.Assert.fail;

import java.io.File;
import java.io.IOException;
import java.util.Set;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import org.junit.Before;
import org.junit.Test;

import com.fr2501.util.StringUtils;
import com.fr2501.virage.analyzer.AdmissionCheckPrologCompositionAnalyzer;
import com.fr2501.virage.analyzer.CompositionAnalyzer;
import com.fr2501.virage.analyzer.SimplePrologCompositionAnalyzer;
import com.fr2501.virage.prolog.ExtendedPrologParser;
import com.fr2501.virage.prolog.MalformedEPLFileException;
import com.fr2501.virage.prolog.QueryState;
import com.fr2501.virage.prolog.SimpleExtendedPrologParser;
import com.fr2501.virage.types.DecompositionTree;
import com.fr2501.virage.types.FrameworkRepresentation;
import com.fr2501.virage.types.Property;
import com.fr2501.virage.types.SearchResult;
import com.fr2501.virage.types.ValueNotPresentException;

public abstract class CompositionAnalyzerTest {
	private static final Logger logger = LogManager.getLogger(CompositionAnalyzerTest.class);
	
	private static final String FRAMEWORK_PATH = "src/main/resources/framework.pl";
	protected TestDataGenerator generator;
	protected FrameworkRepresentation framework;
	
	protected abstract CompositionAnalyzer createInstance();
	
	@Before
	public void setup() throws IOException, MalformedEPLFileException {
		ExtendedPrologParser parser = new SimpleExtendedPrologParser();
		this.framework = parser.parseFramework(new File(FRAMEWORK_PATH));
		
		this.generator = new TestDataGenerator(framework);
	}
	
	@Test
	public void testRandomPropertySets() throws Exception {
		final int RUNS = 100;
		final int TIMEOUT = 10;
		
		int success = 0;
		int timeout = 0;
		int failure = 0;
		int error = 0;
		
		CompositionAnalyzer analyzer = this.createInstance();
		analyzer.setTimeout(TIMEOUT);
		
		for(int i=0; i<RUNS; i++) {
			int amount = (int) (5 * Math.random()) + 1;
			
			Set<Property> properties = this.generator.getRandomComposableModuleProperties(amount);
			
			logger.info(StringUtils.printCollection(properties));
			
			SearchResult<DecompositionTree> result = analyzer.generateComposition(properties);
			
			if(result.hasValue()) {
				success++;
				logger.info("Result: " + result.getValue().toString());
			} else {
				if(result.getState() == QueryState.TIMEOUT) {
					timeout++;
					logger.info("Query timed out.");
				} else if(result.getState() == QueryState.FAILED) {
					failure++;
					logger.info("No solution exists.");
				} else if(result.getState() == QueryState.ERROR) {
					error++;
					logger.error("An error occured");
				}
			}
		}
		
		logger.info("\nSucceeded:\t" + success
				+ "\nFailed:\t\t" + failure
				+ "\nTimed out:\t" + timeout
				+ "\nErrors:\t\t" + error);
		
		if(failure == 100 || success == 100 || timeout == 100) {
			logger.warn("A highly unlikely result occured in the test.\n"
					+ "This might happen by (a very small) chance, so rerunning the test might help.\n"
					+ "If the problem persists, something has gone wrong.");
			fail();
		}
	}
	
	// The SimplePrologCompositionAnalyzer is considered to be correct and
	// is thus used as a baseline for all other implementations of CompositionAnalyzer.
	@Test
	public void testAccordanceWithSPCA() throws ValueNotPresentException {
		SimplePrologCompositionAnalyzer spca = new SimplePrologCompositionAnalyzer(this.framework);
		CompositionAnalyzer self = this.createInstance();
		
		final int RUNS = 100;
		final int TIMEOUT = 10;
		
		spca.setTimeout(TIMEOUT);
		self.setTimeout(TIMEOUT);
		
		int conflicts = 0;
		int errors = 0;
		int improvements = 0;
		
		int selfTimeout = 0;
		int trustedTimeout = 0;
		int selfSuccess = 0;
		int trustedSuccess = 0;
		int selfFailure = 0;
		int trustedFailure = 0;
		
		for(int i=0; i<RUNS; i++) {
			int amount = (int) (5 * Math.random()) + 1;
			
			Set<Property> properties = this.generator.getRandomComposableModuleProperties(amount);
			
			logger.info(StringUtils.printCollection(properties));
			
			SearchResult<DecompositionTree> trustedResult = spca.generateComposition(properties);
			SearchResult<DecompositionTree> result = self.generateComposition(properties);
			
			if(result.getState() == QueryState.ERROR) {
				errors++;
			}
			
			if(trustedResult.getState() == QueryState.FAILED) {
				trustedFailure++;
				if(result.getState() == QueryState.SUCCESS) {
					conflicts++;
					selfSuccess++;
				} else {
					selfFailure++;
				}
			}
			
			if(trustedResult.getState() == QueryState.SUCCESS) {
				trustedSuccess++;
				if(result.getState() == QueryState.FAILED) {
					conflicts++;
					selfFailure++;
				} else {
					selfSuccess++;
				}
			}
			
			if(trustedResult.getState() == QueryState.TIMEOUT) {
				trustedTimeout++;
				if(result.getState() == QueryState.SUCCESS) {
					improvements++;
					selfSuccess++;
				} else if(result.getState() == QueryState.FAILED) {
					improvements++;
					selfFailure++;
				} else {
					selfTimeout++;
				}
			}
			
			
		}
	
		logger.info("Errors: " + errors);
		logger.info("Conflicts: " + conflicts);
		logger.info("Improvements: " + improvements);
		
		if(errors > 0 || conflicts > 0) {
			fail();
		} else {
			logger.info("Trusted:");
			logger.info("\tTimeouts: " + trustedTimeout);
			logger.info("\tFailures: " + trustedFailure);
			logger.info("\tSuccesses: " + trustedSuccess);	
			logger.info("-----");
			logger.info("Self:");
			logger.info("\tTimeouts: " + selfTimeout);
			logger.info("\tFailures: " + selfFailure);
			logger.info("\tSuccesses: " + selfSuccess);
		}
	}
}
