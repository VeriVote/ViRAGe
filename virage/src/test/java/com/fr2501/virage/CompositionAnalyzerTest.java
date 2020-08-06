package com.fr2501.virage;

import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

import java.io.File;
import java.io.IOException;
import java.util.LinkedList;
import java.util.List;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import org.junit.Before;
import org.junit.Test;

import com.fr2501.util.StringUtils;
import com.fr2501.virage.analyzer.CompositionAnalyzer;
import com.fr2501.virage.analyzer.SimplePrologCompositionAnalyzer;
import com.fr2501.virage.prolog.ExtendedPrologParser;
import com.fr2501.virage.prolog.MalformedEPLFileException;
import com.fr2501.virage.prolog.QueryState;
import com.fr2501.virage.prolog.SimpleExtendedPrologParser;
import com.fr2501.virage.types.CompositionProof;
import com.fr2501.virage.types.DecompositionTree;
import com.fr2501.virage.types.FrameworkRepresentation;
import com.fr2501.virage.types.Property;
import com.fr2501.virage.types.SearchResult;
import com.fr2501.virage.types.ValueNotPresentException;

public abstract class CompositionAnalyzerTest {
	private static final Logger logger = LogManager.getLogger(CompositionAnalyzerTest.class);
	
	private static final String FRAMEWORK_PATH = "src/test/resources/framework.pl";
	protected TestDataGenerator generator;
	protected FrameworkRepresentation framework;
	
	protected abstract CompositionAnalyzer createInstance() throws IOException;
	
	@Before
	public void setup() throws IOException, MalformedEPLFileException {
		ExtendedPrologParser parser = new SimpleExtendedPrologParser();
		this.framework = parser.parseFramework(new File(FRAMEWORK_PATH));
		
		this.generator = new TestDataGenerator(framework);
	}
	
	@Test
	public void testSequentialMajorityComparison() throws ValueNotPresentException, IOException {
		logger.info("testSequentialMajorityComparison()");
		String smc = "seq_comp(" + 
						"loop_comp(" + 
							"parallel_comp(" + 
								"seq_comp(" + 
									"pass_module(2,_)," + 
									"seq_comp(" + 
										"downgrade(" + 
											"plurality_module)," + 
										"pass_module(1,_)))," + 
								"drop_module(2,_)," + 
								"max_aggregator)," + 
							"defer_eq_condition(1))," + 
						"elect_module)";
		
		DecompositionTree smcTree = DecompositionTree.parseString(smc);
		
		CompositionAnalyzer analyzer = this.createInstance();
		analyzer.setTimeout(10000);
		
		List<Property> properties = new LinkedList<Property>();
		properties.add(this.framework.getProperty("monotone"));
		
		SearchResult<Boolean> result = analyzer.analyzeComposition(smcTree, properties);
		
		if(result.getState() == QueryState.TIMEOUT) {
			logger.warn("The current CompositionAnalyzer is very slow. "
					+ "This is not an error by definition, but something"
					+ "seems to be wrong.");
		}
		
		assertTrue(result.hasValue());
		assertTrue(result.getValue());
	}
	
	@Test
	public void testRandomPropertySets() throws Exception {
		logger.info("testRandomPropertySets()");
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
			
			List<Property> properties = this.generator.getRandomComposableModuleProperties(amount);
			
			logger.debug("Query: " + StringUtils.printCollection(properties));
			
			SearchResult<DecompositionTree> result = analyzer.generateComposition(properties);
			
			if(result.hasValue()) {
				success++;
				logger.debug("Result: " + result.getValue().toString());
			} else {
				if(result.getState() == QueryState.TIMEOUT) {
					timeout++;
					logger.debug("Query timed out.");
				} else if(result.getState() == QueryState.FAILED) {
					failure++;
					logger.debug("No solution exists.");
				} else if(result.getState() == QueryState.ERROR) {
					error++;
					logger.error("An error occured");
				}
			}
		}
		
		logger.debug("\nSucceeded:\t" + success
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
	public void testAccordanceWithSPCA() throws ValueNotPresentException, IOException {
		logger.info("testAccordanceWithSCPA()");
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
			int amount = (int) (10 * Math.random()) + 1;
			
			List<Property> properties = this.generator.getRandomComposableModuleProperties(amount);
			
			logger.debug("Query: " + StringUtils.printCollection(properties));
			
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
	
		logger.debug("Errors: " + errors);
		logger.debug("Conflicts: " + conflicts);
		logger.debug("Improvements: " + improvements);
		
		if(errors > 0 || conflicts > 0) {
			fail();
		} else {
			logger.debug("Trusted:");
			logger.debug("\tTimeouts: " + trustedTimeout);
			logger.debug("\tFailures: " + trustedFailure);
			logger.debug("\tSuccesses: " + trustedSuccess);	
			logger.debug("-----");
			logger.debug("Self:");
			logger.debug("\tTimeouts: " + selfTimeout);
			logger.debug("\tFailures: " + selfFailure);
			logger.debug("\tSuccesses: " + selfSuccess);
		}
	}
	
	@Test
	public void testSimpleProofs() throws IOException {
		List<Property> properties = new LinkedList<Property>();
		properties.add(this.framework.getProperty("monotone"));
		
		String votingRule = "seq_comp(pass_module(1,_),elect_module)";
		
		CompositionAnalyzer analyzer = this.createInstance();
		
		List<CompositionProof> proof = analyzer.proveClaims(DecompositionTree.parseString(votingRule), properties);
		
		// Prolog variable names are not always the same.
		String proofString = proof.get(0).toString().replaceAll(",_[0-9]+", ",_1");
		
		String reference = ": monotone(seq_comp(pass_module(1,_1),elect_module)) by monotone_sequence\n" + 
				"	: defer_lift_invariant(pass_module(1,_1)) by pass_module_defer_lift_invariant\n" + 
				"	: non_electing(pass_module(1,_1)) by pass_module_non_electing\n" + 
				"	: defers(1,pass_module(1,_1)) by pass_1_module_defers_1\n" + 
				"	: electing(elect_module) by elect_module_electing";
		
		logger.debug(proofString);
		assertTrue(proofString.equals(reference));
	}
}
