package edu.kit.kastel.formal.virage.test.unit;

import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

import java.io.File;
import java.util.LinkedList;
import java.util.List;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import org.junit.Before;
import org.junit.Test;

import edu.kit.kastel.formal.util.Pair;
import edu.kit.kastel.formal.util.StringUtils;
import edu.kit.kastel.formal.util.SystemUtils;
import edu.kit.kastel.formal.virage.analyzer.AdmissionCheckPrologCompositionAnalyzer;
import edu.kit.kastel.formal.virage.analyzer.CompositionAnalyzer;
import edu.kit.kastel.formal.virage.analyzer.SimplePrologCompositionAnalyzer;
import edu.kit.kastel.formal.virage.isabelle.IsabelleProofChecker;
import edu.kit.kastel.formal.virage.isabelle.IsabelleTheoryGenerator;
import edu.kit.kastel.formal.virage.prolog.ExtendedPrologParser;
import edu.kit.kastel.formal.virage.prolog.PrologParser;
import edu.kit.kastel.formal.virage.prolog.QueryState;
import edu.kit.kastel.formal.virage.prolog.SimpleExtendedPrologParser;
import edu.kit.kastel.formal.virage.types.CompositionProof;
import edu.kit.kastel.formal.virage.types.DecompositionTree;
import edu.kit.kastel.formal.virage.types.FrameworkRepresentation;
import edu.kit.kastel.formal.virage.types.Property;
import edu.kit.kastel.formal.virage.types.SearchResult;

/**
 * Test suite for {@link IsabelleProofChecker}.
 *
 * @author VeriVote
 */
public final class IsabelleProofCheckerTest {
    /**
     * Test Prolog predicate name "_".
     */
    private static final String ANY = "_";

    /**
     * Test Prolog predicate name "1".
     */
    private static final String ONE = "1";

    /**
     * Test Prolog predicate name "2".
     */
    private static final String TWO = "2";

    /**
     * Test Prolog predicate name "plurality".
     */
    private static final String PLURALITY = "plurality";

    /**
     * Test Prolog predicate name "elect_module".
     */
    private static final String ELECT = "elect_module";

    /**
     * Test Prolog predicate name "max_aggregator".
     */
    private static final String MAX_AGG = "max_aggregator";

    /**
     * Test Prolog predicate name "defer_equal_condition".
     */
    private static final String DEF_EQ_COND = "defer_equal_condition";

    /**
     * Test Prolog predicate name "pass_module".
     */
    private static final String PASS = "pass_module";

    /**
     * Test Prolog predicate name "drop_module".
     */
    private static final String DROP = "drop_module";

    /**
     * Test Prolog predicate name "sequential_composition".
     */
    private static final String SEQ_COMP = "sequential_composition";

    /**
     * Test Prolog predicate name "revision_composition".
     */
    private static final String REV_COMP = "revision_composition";

    /**
     * Test Prolog predicate name "parallel_composition".
     */
    private static final String PAR_COMP = "parallel_composition";

    /**
     * Test Prolog predicate name "loop_composition".
     */
    private static final String LOOP_COMP = "loop_composition";

    /**
     * Test Prolog predicate name "electing".
     */
    private static final String ELECTING = "electing";

    /**
     * Test Prolog predicate name "monotonicity".
     */
    private static final String MONO = "monotonicity";

    /**
     * String representation of SMC.
     */
    private static final String SMC =
            StringUtils.func(SEQ_COMP,
                    StringUtils.func(LOOP_COMP,
                            StringUtils.func(PAR_COMP,
                                    StringUtils.func(SEQ_COMP,
                                            StringUtils.func(PASS, TWO, ANY),
                                            StringUtils.func(SEQ_COMP,
                                                    StringUtils.func(REV_COMP, PLURALITY),
                                                    StringUtils.func(PASS, ONE, ANY))),
                                    StringUtils.func(DROP, TWO, ANY),
                                    MAX_AGG),
                            StringUtils.func(DEF_EQ_COND, ONE)),
                    ELECT);

    /**
     * The logger.
     */
    private static final Logger LOGGER = LogManager.getLogger(IsabelleProofCheckerTest.class);

    /**
     * Path to an EPL file.
     */
    private static final String EPL_PATH =
            SystemUtils.RESOURCES + "framework" + PrologParser.DOT_PL;

    /**
     * Path to Isabelle theories.
     */
    private static final String THEORY_PATH = SystemUtils.RESOURCES + "old_theories";

    /**
     * A compositional framework.
     */
    private FrameworkRepresentation framework;
    /**
     * The composition analyzer.
     */
    private CompositionAnalyzer analyzer;
    /**
     * The theory generator.
     */
    private IsabelleTheoryGenerator generator;

    /**
     * The generated theory file.
     */
    private File file;

    /**
     * Initialization for the following tests.
     *
     * @throws Exception if something goes wrong
     */
    @Before
    public void init() throws Exception {
        final ExtendedPrologParser parser = new SimpleExtendedPrologParser();
        this.framework = parser.parseFramework(new File(EPL_PATH), false);

        this.analyzer = new SimplePrologCompositionAnalyzer(this.framework);
        this.generator = new IsabelleTheoryGenerator(THEORY_PATH, this.framework);
    }

    /**
     * Prove claims for further use.
     *
     * @param properties the desired properties
     * @param composition the composition
     */
    protected void proveClaims(final List<Property> properties, final String composition) {
        final List<CompositionProof> proofs =
                this.analyzer.proveClaims(DecompositionTree.parseString(composition), properties);
        this.file = this.generator.generateTheoryFile(composition, proofs);
    }

    /**
     * Simple test. <b>Caution:</b> Takes long, not performed by default.
     *
     * @throws Exception if something goes wrong
     */
    @Test
    public void simpleFrameworkTest() throws Exception {
        final List<Property> properties = new LinkedList<Property>();
        properties.add(this.framework.getProperty(ELECTING));

        this.proveClaims(properties, ELECT);

        final IsabelleProofChecker checker = IsabelleProofChecker
                .getInstance(this.framework.getSessionName(), this.framework.getTheoryPath());
        final Pair<Boolean, File> result = checker.verifyTheoryFile(this.file, this.framework);
        assertTrue(result.getFirstValue());
        this.file = result.getSecondValue();

        // Should work twice in a row, second one much faster.
        assertTrue(checker.verifyTheoryFile(this.file, this.framework).getFirstValue());
        checker.destroy();
    }

    // Takes long, not performed by default.
    // Currently, no such module is known for the reworked framework, so test fails.
    /*
     * @Test public void worksWithBlastButNotWithSimpTest() throws IOException, InterruptedException
     * { List<Property> properties = new LinkedList<Property>();
     * properties.add(this.framework.getProperty("non_electing"));
     *
     * proveClaims(properties, "parallel_composition(elect_module,elect_module,max_aggregator)");
     *
     * IsabelleProofChecker checker = IsabelleProofChecker.getInstance(framework.getSessionName(),
     * framework.getTheoryPath()); Pair<Boolean,File> result = checker.verifyTheoryFile(this.file,
     * this.framework); assertTrue(result.getFirstValue()); this.file = result.getSecondValue();
     *
     * // Should work twice in a row, second one much faster.
     * assertTrue(checker.verifyTheoryFile(this.file, this.framework).getFirstValue());
     *
     * checker.destroy(); }
     */

    /**
     * Runs an exemplary proof and check process.
     *
     * @throws Exception if something goes wrong
     */
    // @Test
    public void smcTest() throws Exception {
        final List<Property> properties = new LinkedList<Property>();
        properties.add(this.framework.getProperty(ELECTING));
        properties.add(this.framework.getProperty(MONO));

        this.proveClaims(properties, SMC);

        final IsabelleProofChecker checker = IsabelleProofChecker
                .getInstance(this.framework.getSessionName(), this.framework.getTheoryPath());

        final Pair<Boolean, File> result = checker.verifyTheoryFile(this.file, this.framework);
        assertTrue(result.getFirstValue());
        this.file = result.getSecondValue();

        // Should work twice in a row, second one much faster.
        assertTrue(checker.verifyTheoryFile(this.file, this.framework).getFirstValue());
        checker.destroy();
    }

    /**
     * Runs queries on several random property sets.
     *
     * @throws Exception if something goes wrong
     */
    // @Test
    public void testRandomPropertySets() throws Exception {
        LOGGER.info("testRandomPropertySets()");
        final int runs = 3;
        final int timeout = 10;

        int success = 0;
        int timeouts = 0;
        int failure = 0;
        int error = 0;

        final CompositionAnalyzer localAnalyzer = new AdmissionCheckPrologCompositionAnalyzer(
                this.framework);
        localAnalyzer.setTimeout(timeout);

        final IsabelleProofChecker checker = IsabelleProofChecker
                .getInstance(this.framework.getSessionName(), this.framework.getTheoryPath());

        for (int i = 0; i < runs; i++) {
            final int amount = (int) (5 * Math.random()) + 1;

            final TestDataGenerator localGenerator = new TestDataGenerator(this.framework);
            final List<Property> properties =
                    localGenerator.getRandomComposableModuleProperties(amount);

            LOGGER.debug("Query: " + StringUtils.printCollection(properties));

            final SearchResult<DecompositionTree> result =
                    localAnalyzer.generateComposition(properties);

            if (result.hasValue()) {
                success++;
                LOGGER.debug("Result: " + result.getValue().toString());
                this.proveClaims(properties, result.getValue().toString());
                checker.verifyTheoryFile(this.file, this.framework);
            } else {
                if (result.getState() == QueryState.TIMEOUT) {
                    timeouts++;
                    LOGGER.debug("Query timed out.");
                } else if (result.getState() == QueryState.FAILED) {
                    failure++;
                    LOGGER.debug("No solution exists.");
                } else if (result.getState() == QueryState.ERROR) {
                    error++;
                    LOGGER.error("An error occured");
                }
            }
        }
        LOGGER.debug("\nSucceeded:\t" + success + "\nFailed:\t\t" + failure + "\nTimed out:\t"
                + timeouts + "\nErrors:\t\t" + error);
        if (failure == runs || success == runs || timeouts == runs) {
            LOGGER.warn("A highly unlikely result occured in the test.\n"
                    + "This might happen by (a very small) chance, "
                    + "so rerunning the test might help.\n"
                    + "If the problem persists, something has gone wrong.");
            fail();
        }
    }
}
