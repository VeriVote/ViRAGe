package edu.kit.kastel.formal.virage.test.unit;

import java.io.File;
import java.io.IOException;
import java.util.LinkedList;

import org.junit.Before;
import org.junit.Test;

import edu.kit.kastel.formal.util.StringUtils;
import edu.kit.kastel.formal.util.SystemUtils;
import edu.kit.kastel.formal.virage.isabelle.IsabelleCodeGenerator;
import edu.kit.kastel.formal.virage.isabelle.IsabelleTheoryGenerator;
import edu.kit.kastel.formal.virage.prolog.ExtendedPrologParser;
import edu.kit.kastel.formal.virage.prolog.MalformedEplFileException;
import edu.kit.kastel.formal.virage.prolog.PrologParser;
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
    private static final String EPL_PATH =
            SystemUtils.RESOURCES + "framework_new" + PrologParser.DOT_PL;

    /**
     * Path to Isabelle theories.
     */
    private static final String THEORY_PATH =
            SystemUtils.RESOURCES + "verifiedVotingRuleConstruction/theories";

    /**
     * String representation of elect module.
     */
    private static final String ELECT = "elect_module";

    /**
     * String representation of one.
     */
    private static final String ONE = "1";

    /**
     * String representation of two.
     */
    private static final String TWO = "2";

    /**
     * String representation of a placeholder sign.
     */
    private static final String PLACEHOLDER = "_";

    /**
     * String representation of drop module.
     */
    private static final String DROP_STRING = "drop_module";

    /**
     * String representation of pass module.
     */
    private static final String PASS_STRING = "pass_module";

    /**
     * String representation of plurality module.
     */
    private static final String PLURALITY = "plurality";

    /**
     * String representation of sequential composition.
     */
    private static final String SEQ_COMP = "sequential_composition";

    /**
     * String representation of revision composition.
     */
    private static final String REV_COMP = "revision_composition";

    /**
     * String representation of maximum aggregation structure.
     */
    private static final String MAX_AGG = "max_aggregator";

    /**
     * String representation of parallel composition.
     */
    private static final String PAR_COMP = "parallel_composition";

    /**
     * String representation of loop composition.
     */
    private static final String LOOP_COMP = "loop_composition";

    /**
     * String representation of defer equals one condition.
     */
    private static final String DEF_EQ_ONE = StringUtils.func("defer_equal_condition", ONE);

    /**
     * String representation of SMC.
     */
    private static final String SMC =
            StringUtils.func(SEQ_COMP,
                    StringUtils.func(LOOP_COMP,
                            StringUtils.func(PAR_COMP,
                                    StringUtils.func(SEQ_COMP,
                                            passModule(TWO),
                                            StringUtils.func(SEQ_COMP,
                                                    StringUtils.func(REV_COMP, PLURALITY),
                                                    passModule(ONE))),
                                    dropModule(TWO), MAX_AGG),
                            DEF_EQ_ONE),
                    ELECT);

    /**
     * A compositional framework.
     */
    private FrameworkRepresentation framework;

    /**
     * The theory generator.
     */
    private IsabelleTheoryGenerator generator;

    private static String dropModule(final String number) {
        return StringUtils.func(DROP_STRING, number, PLACEHOLDER);
    }

    private static String passModule(final String number) {
        return StringUtils.func(PASS_STRING, number, PLACEHOLDER);
    }

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
     *
     * @throws Exception if something goes wrong.
     */
    @Test
    public void electTest() throws Exception {
        final IsabelleCodeGenerator codeGenerator = new IsabelleCodeGenerator(this.framework);
        final File theory =
                this.generator.generateTheoryFile(ELECT, new LinkedList<CompositionProof>());
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
        codeGenerator.generateScalaCodeAndCompile(dropModule(ONE));
    }

    /**
     * Test based on plurality_module.
     *
     * @throws Exception if something goes wrong
     */
    @Test
    public void pluralityTest() throws Exception {
        final IsabelleCodeGenerator codeGenerator = new IsabelleCodeGenerator(this.framework);
        final File theory =
                this.generator.generateTheoryFile(PLURALITY, new LinkedList<CompositionProof>());
        codeGenerator.generateScalaCodeAndCompile(theory);
    }

    /**
     * Test based on sequential majority comparison (SMC).
     *
     * @throws Exception if something goes wrong
     */
    @Test
    public void smcTest() throws Exception {
        final IsabelleCodeGenerator codeGenerator = new IsabelleCodeGenerator(this.framework);
        final String module = SMC;
        final File theory =
                this.generator.generateTheoryFile(module, new LinkedList<CompositionProof>());
        codeGenerator.generateScalaCodeAndCompile(theory);
    }
}
