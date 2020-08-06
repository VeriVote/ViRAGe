package com.fr2501.virage;

import static org.junit.Assert.fail;

import java.io.File;
import java.io.IOException;
import java.util.LinkedList;
import java.util.List;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import org.junit.Before;
import org.junit.Test;

import com.fr2501.virage.analyzer.CompositionAnalyzer;
import com.fr2501.virage.analyzer.SimplePrologCompositionAnalyzer;
import com.fr2501.virage.isabelle.IsabelleTheoryGenerator;
import com.fr2501.virage.prolog.ExtendedPrologParser;
import com.fr2501.virage.prolog.MalformedEPLFileException;
import com.fr2501.virage.prolog.SimpleExtendedPrologParser;
import com.fr2501.virage.types.CompositionProof;
import com.fr2501.virage.types.DecompositionTree;
import com.fr2501.virage.types.FrameworkRepresentation;
import com.fr2501.virage.types.Property;

public class IsabelleTheoryGeneratorTest {
	private static final Logger logger = LogManager.getLogger(IsabelleTheoryGeneratorTest.class);
	
	private static final String PATH = "src/test/resources/framework.pl";
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
	
	@Before
	public void init() throws IOException, MalformedEPLFileException {
		ExtendedPrologParser parser = new SimpleExtendedPrologParser();
		this.framework = parser.parseFramework(new File(PATH));
		
		this.analyzer = new SimplePrologCompositionAnalyzer(this.framework);
	}
	
	@Test
	public void testSMCProof() throws IOException, MalformedEPLFileException {
		List<Property> properties = new LinkedList<Property>();
		properties.add(this.framework.getProperty("electoral_module"));
		properties.add(this.framework.getProperty("monotone"));
		properties.add(this.framework.getProperty("electing"));
		
		proveClaims(properties, SMC);
	}
	
	@Test
	public void testVerySimpleProof() {
		List<Property> properties = new LinkedList<Property>();
		properties.add(this.framework.getProperty("electoral_module"));
		properties.add(this.framework.getProperty("electing"));
		
		proveClaims(properties, "elect_module");
	}
	
	@Test
	public void testSimpleProof() {
		List<Property> properties = new LinkedList<Property>();
		properties.add(this.framework.getProperty("electoral_module"));
		properties.add(this.framework.getProperty("electing"));
		properties.add(this.framework.getProperty("monotone"));
		
		proveClaims(properties, "seq_comp(pass_module(1,_),elect_module)");
	}
	
	@Test
	public void testCondorcetProof() {
		List<Property> properties = new LinkedList<Property>();
		properties.add(this.framework.getProperty("electoral_module"));
		properties.add(this.framework.getProperty("condorcet_consistent"));
		
		proveClaims(properties, "seq_comp(elimination_module(copeland_score,max,less), elect_module)");
	}
	
	protected void proveClaims(List<Property> properties, String composition) {
		List<CompositionProof> proofs = analyzer.proveClaims(new DecompositionTree(composition), properties);

		IsabelleTheoryGenerator generator = new IsabelleTheoryGenerator("src/test/resources/theories/", this.framework);
		
		try {
			File file = File.createTempFile("tmp", ".thy");
			file.deleteOnExit();
			
			generator.generateTheoryFile(file.getAbsolutePath(), composition, proofs);
		} catch (IOException e) {
			logger.error("Something went wrong.", e);
			fail();
		}
	}
}
