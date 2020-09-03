package com.fr2501.virage.test.unit;

import java.io.File;
import java.io.IOException;
import java.util.LinkedList;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import org.junit.Before;
import org.junit.Test;

import com.fr2501.virage.analyzer.CompositionAnalyzer;
import com.fr2501.virage.analyzer.SimplePrologCompositionAnalyzer;
import com.fr2501.virage.isabelle.IsabelleCodeGenerator;
import com.fr2501.virage.isabelle.IsabelleTheoryGenerator;
import com.fr2501.virage.prolog.ExtendedPrologParser;
import com.fr2501.virage.prolog.MalformedEPLFileException;
import com.fr2501.virage.prolog.SimpleExtendedPrologParser;
import com.fr2501.virage.types.CompositionProof;
import com.fr2501.virage.types.DecompositionTree;
import com.fr2501.virage.types.FrameworkRepresentation;

public class IsabelleCodeGeneratorTest {
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
	
	@Before
	public void init() throws IOException, MalformedEPLFileException {
		ExtendedPrologParser parser = new SimpleExtendedPrologParser();
		this.framework = parser.parseFramework(new File(EPL_PATH));
		
		this.analyzer = new SimplePrologCompositionAnalyzer(this.framework);
		this.generator = new IsabelleTheoryGenerator(THEORY_PATH, this.framework);
	}
	
	@Test
	public void simpleTest() throws IOException, InterruptedException {
		IsabelleCodeGenerator codeGenerator = new IsabelleCodeGenerator(this.framework);
		
		String module = "elect_module";
	
		File theory = this.generator.generateTheoryFile(module, new LinkedList<CompositionProof>());
		
		codeGenerator.generateScalaCode(theory);
	}
}
