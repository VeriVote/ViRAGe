package com.fr2501.virage.test.unit;

import java.io.File;
import java.io.IOException;
import java.util.LinkedList;

import org.junit.Before;
import org.junit.Test;

import com.fr2501.virage.isabelle.IsabelleCodeGenerator;
import com.fr2501.virage.isabelle.IsabelleTheoryGenerator;
import com.fr2501.virage.prolog.ExtendedPrologParser;
import com.fr2501.virage.prolog.MalformedEplFileException;
import com.fr2501.virage.prolog.SimpleExtendedPrologParser;
import com.fr2501.virage.types.CompilationFailedException;
import com.fr2501.virage.types.CompositionProof;
import com.fr2501.virage.types.ExternalSoftwareUnavailableException;
import com.fr2501.virage.types.FrameworkRepresentation;
import com.fr2501.virage.types.IsabelleBuildFailedException;

/**
 * A test suite for {@link IsabelleCodeGenerator}.
 *
 */
public class IsabelleCodeGeneratorTest {
    /**
     * Path to an (E)PL file.
     */
    private static final String EPL_PATH = "src/test/resources/framework_new.pl";
    /**
     * Path to Isabelle theories.
     */
    private static final String THEORY_PATH =
            "src/test/resources/verifiedVotingRuleConstruction/theories";
    /**
     * String representation of SMC.
     */
    private static final String SMC = "sequential_composition(loop_composition("
            + "parallel_composition(" + "sequential_composition(pass_module(2,_),"
            + "sequential_composition(" + "revision_composition(" + "plurality),"
            + "pass_module(1,_)))," + "drop_module(2,_)," + "max_aggregator),"
            + "defer_equal_condition(1))," + "elect_module)";
    /**
     * A compositional framework.
     */
    private FrameworkRepresentation framework;
    /**
     * The theory generator.
     */
    private IsabelleTheoryGenerator generator;

    /**
     * Initialization for the following tests.
     *
     * @throws IOException if file interaction fails
     * @throws MalformedEplFileException if input file is not valid EPL
     */
    @Before
    public void init() throws IOException, MalformedEplFileException {
        final ExtendedPrologParser parser = new SimpleExtendedPrologParser();
        this.framework = parser.parseFramework(new File(EPL_PATH), false);

        this.generator = new IsabelleTheoryGenerator(THEORY_PATH, this.framework);
    }

    /**
     * Test based on elect_module.
     * @throws IOException if io fails.
     * @throws InterruptedException if thread is interrupted
     * @throws CompilationFailedException if the code cannot be compiled
     * @throws IsabelleBuildFailedException if the Isabelle build process fails
     * @throws ExternalSoftwareUnavailableException if Isabelle is unavailable
     */
    @Test
    public void electTest() throws IOException, InterruptedException, CompilationFailedException,
            IsabelleBuildFailedException, ExternalSoftwareUnavailableException {
        final IsabelleCodeGenerator codeGenerator = new IsabelleCodeGenerator(this.framework);

        final String module = "elect_module";

        final File theory = this.generator.generateTheoryFile(module,
                new LinkedList<CompositionProof>());

        codeGenerator.generateScalaCodeAndCompile(theory);
    }

    /**
     * Test based on drop_module.
     * @throws IOException if io fails.
     * @throws InterruptedException if thread is interrupted
     * @throws CompilationFailedException if the code cannot be compiled
     * @throws IsabelleBuildFailedException if the Isabelle build process fails
     * @throws ExternalSoftwareUnavailableException if Isabelle is unavailable
     */
    @Test
    public void dropTest() throws IOException, InterruptedException, CompilationFailedException,
            IsabelleBuildFailedException, ExternalSoftwareUnavailableException {
        final IsabelleCodeGenerator codeGenerator = new IsabelleCodeGenerator(this.framework);

        final String module = "drop_module(1,_)";

        codeGenerator.generateScalaCodeAndCompile(module);
    }

    /**
     * Test based on plurality_module.
     * @throws IOException if io fails.
     * @throws InterruptedException if thread is interrupted
     * @throws CompilationFailedException if the code cannot be compiled
     * @throws IsabelleBuildFailedException if the Isabelle build process fails
     * @throws ExternalSoftwareUnavailableException if Isabelle is unavailable
     */
    @Test
    public void pluralityTest()
            throws IOException, InterruptedException, CompilationFailedException,
            IsabelleBuildFailedException, ExternalSoftwareUnavailableException {
        final IsabelleCodeGenerator codeGenerator = new IsabelleCodeGenerator(this.framework);

        final String module = "plurality";

        final File theory = this.generator.generateTheoryFile(module,
                new LinkedList<CompositionProof>());

        codeGenerator.generateScalaCodeAndCompile(theory);
    }

    /**
     * Test based on smc.
     * @throws IOException if io fails.
     * @throws InterruptedException if thread is interrupted
     * @throws CompilationFailedException if the code cannot be compiled
     * @throws IsabelleBuildFailedException if the Isabelle build process fails
     * @throws ExternalSoftwareUnavailableException if Isabelle is unavailable
     */
    @Test
    public void smcTest() throws IOException, InterruptedException, CompilationFailedException,
            IsabelleBuildFailedException, ExternalSoftwareUnavailableException {
        final IsabelleCodeGenerator codeGenerator = new IsabelleCodeGenerator(this.framework);

        final String module = SMC;

        final File theory = this.generator.generateTheoryFile(module,
                new LinkedList<CompositionProof>());

        codeGenerator.generateScalaCodeAndCompile(theory);
    }
}
