package com.fr2501.virage;

import static org.junit.Assert.assertTrue;

import java.io.File;
import java.io.IOException;
import java.util.LinkedList;
import java.util.List;

import org.junit.Before;
import org.junit.Test;

import com.fr2501.virage.analyzer.CompositionAnalyzer;
import com.fr2501.virage.analyzer.SimplePrologCompositionAnalyzer;
import com.fr2501.virage.isabelle.IsabelleProofChecker;
import com.fr2501.virage.isabelle.IsabelleTheoryGenerator;
import com.fr2501.virage.prolog.ExtendedPrologParser;
import com.fr2501.virage.prolog.MalformedEPLFileException;
import com.fr2501.virage.prolog.SimpleExtendedPrologParser;
import com.fr2501.virage.types.CompositionProof;
import com.fr2501.virage.types.DecompositionTree;
import com.fr2501.virage.types.FrameworkRepresentation;
import com.fr2501.virage.types.Property;

public class IsabelleProofCheckerTest {
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
	
	private String filePath;
	
	@Before
	public void init() throws IOException, MalformedEPLFileException {
		ExtendedPrologParser parser = new SimpleExtendedPrologParser();
		this.framework = parser.parseFramework(new File(EPL_PATH));
		
		this.analyzer = new SimplePrologCompositionAnalyzer(this.framework);
		this.generator = new IsabelleTheoryGenerator(THEORY_PATH, this.framework);
	}
	
	@Test
	public void simpleTest() throws IOException, InterruptedException {
		IsabelleProofChecker checker = new IsabelleProofChecker();
		
		assertTrue(checker.verifyTheoryFile("Main"));
	}
	
	@Test
	public void simpleFrameworkTest() throws IOException, InterruptedException {
		List<Property> properties = new LinkedList<Property>();
		properties.add(this.framework.getProperty("electoral_module"));
		properties.add(this.framework.getProperty("electing"));
		
		proveClaims(properties, "elect_module");
		
		IsabelleProofChecker checker = new IsabelleProofChecker();
		assertTrue(checker.verifyTheoryFile(this.filePath));
	}
	
	@Test
	public void SMCTest() throws IOException, InterruptedException {
		List<Property> properties = new LinkedList<Property>();
		properties.add(this.framework.getProperty("electoral_module"));
		properties.add(this.framework.getProperty("electing"));
		properties.add(this.framework.getProperty("monotone"));
		
		proveClaims(properties, SMC);
		
		IsabelleProofChecker checker = new IsabelleProofChecker();
		checker.verifyTheoryFile(this.filePath);
	}
	
	protected void proveClaims(List<Property> properties, String composition) {
		List<CompositionProof> proofs = analyzer.proveClaims(new DecompositionTree(composition), properties);
			
		this.filePath = generator.generateTheoryFile(THEORY_PATH, composition, proofs);
	}
}
