package com.fr2501.virage.test.unit;

import java.io.File;
import java.io.IOException;
import java.util.LinkedList;

import org.junit.Before;
import org.junit.Test;

import com.fr2501.virage.isabelle.IsabelleCodeGenerator;
import com.fr2501.virage.isabelle.IsabelleTheoryGenerator;
import com.fr2501.virage.prolog.ExtendedPrologParser;
import com.fr2501.virage.prolog.MalformedEPLFileException;
import com.fr2501.virage.prolog.SimpleExtendedPrologParser;
import com.fr2501.virage.types.CompilationFailedException;
import com.fr2501.virage.types.CompositionProof;
import com.fr2501.virage.types.FrameworkRepresentation;
import com.fr2501.virage.types.IsabelleBuildFailedException;

public class IsabelleCodeGeneratorTest {
	private static final String EPL_PATH = "src/test/resources/framework_new.pl";
	private static final String THEORY_PATH = "src/test/resources/verifiedVotingRuleConstruction/theories";
	private static final String SMC = 	"sequential_composition(" + 
											"loop_composition(" + 
											"parallel_composition(" + 
												"sequential_composition(" + 
													"pass_module(2,_)," + 
													"sequential_composition(" + 
														"revision_composition(" + 
															"plurality)," + 
														"pass_module(1,_)))," + 
												"drop_module(2,_)," + 
												"max_aggregator)," + 
											"defer_equal_condition(1))," + 
										"elect_module)";
	private FrameworkRepresentation framework;
	private IsabelleTheoryGenerator generator;
	
	@Before
	public void init() throws IOException, MalformedEPLFileException {
		ExtendedPrologParser parser = new SimpleExtendedPrologParser();
		this.framework = parser.parseFramework(new File(EPL_PATH), false);
		
		this.generator = new IsabelleTheoryGenerator(THEORY_PATH, this.framework);
	}
	
	@Test
	public void electTest() throws IOException, InterruptedException, CompilationFailedException, IsabelleBuildFailedException {
		IsabelleCodeGenerator codeGenerator = new IsabelleCodeGenerator(this.framework);
		
		String module = "elect_module";
	
		File theory = this.generator.generateTheoryFile(module, new LinkedList<CompositionProof>());
		
		codeGenerator.generateScalaCodeAndCompile(theory);
	}
	
	@Test
	public void dropTest() throws IOException, InterruptedException, CompilationFailedException, IsabelleBuildFailedException {
		IsabelleCodeGenerator codeGenerator = new IsabelleCodeGenerator(this.framework);
		
		String module = "drop_module(1,_)";
		
		codeGenerator.generateScalaCodeAndCompile(module);
	}
	
	@Test
	public void pluralityTest() throws IOException, InterruptedException, CompilationFailedException, IsabelleBuildFailedException {
		IsabelleCodeGenerator codeGenerator = new IsabelleCodeGenerator(this.framework);
		
		String module = "plurality";
	
		File theory = this.generator.generateTheoryFile(module, new LinkedList<CompositionProof>());
		
		codeGenerator.generateScalaCodeAndCompile(theory);
	}
	
	@Test
	public void smcTest() throws IOException, InterruptedException, CompilationFailedException, IsabelleBuildFailedException {
		IsabelleCodeGenerator codeGenerator = new IsabelleCodeGenerator(this.framework);
		
		String module = SMC;
	
		File theory = this.generator.generateTheoryFile(module, new LinkedList<CompositionProof>());
		
		codeGenerator.generateScalaCodeAndCompile(theory);
	}
}
