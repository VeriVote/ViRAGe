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
import com.fr2501.virage.analyzer.AdmissionCheckPrologCompositionAnalyzer;
import com.fr2501.virage.analyzer.CompositionAnalyzer;
import com.fr2501.virage.analyzer.SimplePrologCompositionAnalyzer;
import com.fr2501.virage.isabelle.IsabelleProofChecker;
import com.fr2501.virage.isabelle.IsabelleTheoryGenerator;
import com.fr2501.virage.prolog.ExtendedPrologParser;
import com.fr2501.virage.prolog.MalformedEPLFileException;
import com.fr2501.virage.prolog.QueryState;
import com.fr2501.virage.prolog.SimpleExtendedPrologParser;
import com.fr2501.virage.types.CompositionProof;
import com.fr2501.virage.types.DecompositionTree;
import com.fr2501.virage.types.FrameworkRepresentation;
import com.fr2501.virage.types.Property;
import com.fr2501.virage.types.SearchResult;

public class IsabelleProofCheckerTest {
	private static final Logger logger = LogManager.getLogger(IsabelleProofCheckerTest.class);
	
	private static final String EPL_PATH = "src/test/resources/framework.pl";
	private static final String THEORY_PATH = "src/test/resources/theories";
	private static final String SMC = 	"seq_comp(" + 
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
	private FrameworkRepresentation framework;
	private CompositionAnalyzer analyzer;
	private IsabelleTheoryGenerator generator;
	
	private File file;
	
	@Before
	public void init() throws IOException, MalformedEPLFileException {
		ExtendedPrologParser parser = new SimpleExtendedPrologParser();
		this.framework = parser.parseFramework(new File(EPL_PATH));
		
		this.analyzer = new SimplePrologCompositionAnalyzer(this.framework);
		this.generator = new IsabelleTheoryGenerator(THEORY_PATH, this.framework);
	}
	
	//@Test
	public void simpleTest() throws IOException, InterruptedException {
		IsabelleProofChecker checker = IsabelleProofChecker.getInstance();
		
		assertTrue(checker.verifyTheoryFile("Main"));
		
		checker.destroy();
	}
	
	//@Test
	public void testRandomPropertySets() throws Exception {
		logger.info("testRandomPropertySets()");
		final int RUNS = 3;
		final int TIMEOUT = 10;
		
		int success = 0;
		int timeout = 0;
		int failure = 0;
		int error = 0;
		
		CompositionAnalyzer analyzer = new AdmissionCheckPrologCompositionAnalyzer(this.framework);
		analyzer.setTimeout(TIMEOUT);
		
		IsabelleProofChecker checker = IsabelleProofChecker.getInstance();
		
		for(int i=0; i<RUNS; i++) {
			int amount = (int) (5 * Math.random()) + 1;
			
			TestDataGenerator generator = new TestDataGenerator(this.framework);
			List<Property> properties = generator.getRandomComposableModuleProperties(amount);
			
			logger.debug("Query: " + StringUtils.printCollection(properties));
			
			SearchResult<DecompositionTree> result = analyzer.generateComposition(properties);
			
			if(result.hasValue()) {
				success++;
				logger.debug("Result: " + result.getValue().toString());
				
				proveClaims(properties, result.getValue().toString());
				
				checker.verifyTheoryFile(this.file.getAbsolutePath());
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
	
	// Takes long, not performed by default.
	// @Test
	public void simpleFrameworkTest() throws IOException, InterruptedException {
		List<Property> properties = new LinkedList<Property>();
		properties.add(this.framework.getProperty("electoral_module"));
		properties.add(this.framework.getProperty("electing"));
		
		proveClaims(properties, "elect_module");
		
		IsabelleProofChecker checker = IsabelleProofChecker.getInstance();
		assertTrue(checker.verifyTheoryFile(this.file.getAbsolutePath()));
		
		// Should work twice in a row, second one much faster.
		assertTrue(checker.verifyTheoryFile(this.file.getAbsolutePath()));
		
		checker.destroy();
	}
	
	// Takes long, not performed by default.
	@Test
	public void SMCTest() throws IOException, InterruptedException {
		List<Property> properties = new LinkedList<Property>();
		properties.add(this.framework.getProperty("electoral_module"));
		//properties.add(this.framework.getProperty("electing"));
		//properties.add(this.framework.getProperty("monotone"));
		
		proveClaims(properties, "parallel_comp(elect_module,elect_module,max_aggregator)");
		
		IsabelleProofChecker checker = IsabelleProofChecker.getInstance();
		assertTrue(checker.verifyTheoryFile(this.file.getAbsolutePath()));
		
		assertTrue(checker.verifyTheoryFile(this.file.getAbsolutePath()));
		assertTrue(checker.verifyTheoryFile(this.file.getAbsolutePath()));
		assertTrue(checker.verifyTheoryFile(this.file.getAbsolutePath()));
		assertTrue(checker.verifyTheoryFile(this.file.getAbsolutePath()));
		
		checker.destroy();
	}
	
	protected void proveClaims(List<Property> properties, String composition) {
		List<CompositionProof> proofs = analyzer.proveClaims(new DecompositionTree(composition), properties);
			
		this.file = generator.generateTheoryFile(THEORY_PATH, composition, proofs);
	}
}
