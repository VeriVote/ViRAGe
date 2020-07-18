package com.fr2501.virage;

import java.io.File;
import java.io.IOException;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import org.junit.Before;
import org.junit.Test;

import com.fr2501.virage.analyzer.AdmissionCheckPrologCompositionAnalyzer;
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
import com.fr2501.virage.types.SearchResult;

public class IsabelleTheoryGeneratorTest {
	private static final String PATH = "src/test/resources/framework.pl";
	private static final String SMC = 	"sequential_composition(" + 
											"loop_composition(" + 
											"parallel_composition(" + 
												"sequential_composition(" + 
													"pass_module(2)," + 
													"sequential_composition(" + 
														"downgrade(" + 
															"plurality_module)," + 
														"pass_module(1)))," + 
												"drop_module(2)," + 
												"max_aggregator)," + 
											"defer_eq_condition(1))," + 
										"elect_module)";
	private FrameworkRepresentation framework;
	private List<CompositionProof> smcProofs;
	
	@Before
	public void init() throws IOException, MalformedEPLFileException {
		ExtendedPrologParser parser = new SimpleExtendedPrologParser();
		this.framework = parser.parseFramework(new File(PATH));
		
		CompositionAnalyzer analyzer = new SimplePrologCompositionAnalyzer(this.framework);
		
		List<Property> properties = new LinkedList<Property>();
		properties.add(this.framework.getProperty("monotone"));
		properties.add(this.framework.getProperty("electing"));
		
		this.smcProofs = analyzer.proveClaims(new DecompositionTree(SMC), properties);
	}
	
	@Test
	public void simpleProof() {
		IsabelleTheoryGenerator generator = new IsabelleTheoryGenerator();
		
		generator.generateTheoryFile("", "", new LinkedList<CompositionProof>());
	}
	
	@Test
	public void SMCProof() {
		IsabelleTheoryGenerator generator = new IsabelleTheoryGenerator();
		
		generator.generateTheoryFile("", SMC, this.smcProofs);
	}
}
