package edu.kit.kastel.formal.virage.test.unit;

import java.io.File;
import java.io.IOException;
import java.util.LinkedList;

import org.junit.Before;
import org.junit.Test;

import edu.kit.kastel.formal.virage.isabelle.IsabelleCodeGenerator;
import edu.kit.kastel.formal.virage.isabelle.IsabelleTheoryGenerator;
import edu.kit.kastel.formal.virage.prolog.ExtendedPrologParser;
import edu.kit.kastel.formal.virage.prolog.MalformedEplFileException;
import edu.kit.kastel.formal.virage.prolog.SimpleExtendedPrologParser;
import edu.kit.kastel.formal.virage.types.CompositionProof;
import edu.kit.kastel.formal.virage.types.FrameworkRepresentation;

/**
 * A test suite for {@link IsabelleCodeGenerator}.
 *
 * @author VeriVote
 */
public class IsabelleCodeGeneratorTest {
    /**
     * Path to an (E)PL file.
     */
    private static final String EPL_PATH = "src/test/resources/framework_new.pl";
    /**
     * Path to Isabelle theories.
     */
    private static final String THEORY_PATH
        = "src/test/resources/verifiedVotingRuleConstruction/theories";
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
     * @throws Exception if something goes wrong.
     */
    @Test
    public void electTest() throws Exception {
        final IsabelleCodeGenerator codeGenerator = new IsabelleCodeGenerator(this.framework);

        final String module = "elect_module";

        final File theory = this.generator.generateTheoryFile(module,
                new LinkedList<CompositionProof>());

        codeGenerator.generateScalaCodeAndCompile(theory);
    }

    /**
     * Test based on drop_module.
     *
     * @throws Exception if something goes wrong
     */
    @Test
    public void dropTest() throws Exception {
        final IsabelleCodeGenerator codeGenerator = new IsabelleCodeGenerator(this.framework);

        final String module = "drop_module(1,_)";

        codeGenerator.generateScalaCodeAndCompile(module);
    }

    /**
     * Test based on plurality_module.
     *
     * @throws Exception if something goes wrong
     */
    @Test
    public void pluralityTest()
            throws Exception {
        final IsabelleCodeGenerator codeGenerator = new IsabelleCodeGenerator(this.framework);

        final String module = "plurality";

        final File theory = this.generator.generateTheoryFile(module,
                new LinkedList<CompositionProof>());

        codeGenerator.generateScalaCodeAndCompile(theory);
    }

    /**
     * Test based on smc.
     *
     * @throws Exception if something goes wrong
     */
    @Test
    public void smcTest() throws Exception {
        final IsabelleCodeGenerator codeGenerator = new IsabelleCodeGenerator(this.framework);

        final String module = SMC;

        final File theory = this.generator.generateTheoryFile(module,
                new LinkedList<CompositionProof>());

        codeGenerator.generateScalaCodeAndCompile(theory);
    }
}
