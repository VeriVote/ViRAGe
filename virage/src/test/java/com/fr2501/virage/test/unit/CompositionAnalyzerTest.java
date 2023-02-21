package com.fr2501.virage.test.unit;

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
import com.fr2501.virage.analyzer.CompositionAnalyzer;
import com.fr2501.virage.analyzer.SimplePrologCompositionAnalyzer;
import com.fr2501.virage.prolog.ExtendedPrologParser;
import com.fr2501.virage.prolog.MalformedEplFileException;
import com.fr2501.virage.prolog.QueryState;
import com.fr2501.virage.prolog.SimpleExtendedPrologParser;
import com.fr2501.virage.types.BooleanWithUncertainty;
import com.fr2501.virage.types.CompositionProof;
import com.fr2501.virage.types.DecompositionTree;
import com.fr2501.virage.types.ExternalSoftwareUnavailableException;
import com.fr2501.virage.types.FrameworkRepresentation;
import com.fr2501.virage.types.Property;
import com.fr2501.virage.types.SearchResult;

/**
 * Tests that each implementation of {@link CompositionAnalyzer} must pass.
 *
 * @author VeriVote
 */
public abstract class CompositionAnalyzerTest {
    /**
     * Test Prolog predicate name "".
     */
    private static final String EMPTY = "";

    /**
     * Test Prolog predicate name ",".
     */
    private static final String COMMA = ",";

    /**
     * Test Prolog predicate name "\t: ".
     */
    private static final String TAB_COLON = "\t: ";

    /**
     * Test Prolog predicate name "_".
     */
    private static final String ANY = "_";

    /**
     * Test Prolog predicate name "R".
     */
    private static final String R = "R";

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
     * Test Prolog predicate name "defer_lift_invariance".
     */
    private static final String DEFER_LIFT_INV = "defer_lift_invariance";

    /**
     * Test Prolog predicate name "defers".
     */
    private static final String DEFERS = "defers";

    /**
     * Test Prolog predicate name "electing".
     */
    private static final String ELECTING = "electing";

    /**
     * Test Prolog predicate name "non_electing".
     */
    private static final String NON_ELECTING = "non_electing";

    /**
     * Test Prolog predicate name "monotonicity".
     */
    private static final String MONO = "monotonicity";

    /**
     * String representation of SMC.
     */
    private static final String SMC =
        predicate(SEQ_COMP,
                  predicate(LOOP_COMP,
                            predicate(PAR_COMP,
                                      predicate(SEQ_COMP,
                                                predicate(PASS, TWO, ANY),
                                                predicate(SEQ_COMP,
                                                          predicate(REV_COMP, PLURALITY),
                                                          predicate(PASS, ONE, ANY))),
                                      predicate(DROP, TWO, ANY),
                                      MAX_AGG),
                            predicate(DEF_EQ_COND, ONE)),
                  ELECT);

    /**
     * The default timeout for the tests.
     */
    private static final long DEFAULT_TIMEOUT = 10000;

    /**
     * The logger.
     */
    private static final Logger LOGGER = LogManager.getLogger(CompositionAnalyzerTest.class);

    /**
     * Path to an (E)PL file.
     */
    private static final String FRAMEWORK_PATH = "src/test/resources/framework.pl";

    /**
     * The test data generator.
     */
    private TestDataGenerator generator;

    /**
     * The framework representation.
     */
    private FrameworkRepresentation framework;

    /**
     * Translates a predicate to a test Prolog fact.
     *
     * @param pred the predicate of the composed fact
     * @return a test String representing the composed Prolog fact
     */
    private static String fact(final String pred) {
        return pred + ".";
    }

    /**
     * Translates a predicate name and arguments to a test Prolog predicate.
     *
     * @param name the predicate name of the composed predicate
     * @param args the predicate's arguments
     * @return a test String representing the composed Prolog predicate
     */
    private static String predicate(final String name, final String... args) {
        String arg = EMPTY;
        for (final String a : args) {
            if (!arg.isEmpty()) {
                arg += COMMA;
            }
            arg += a;
        }
        return "name" + "(" + arg + ")";
    }

    /**
     * Translates a head predicate and various body predicates to a test Prolog clause.
     *
     * @param head the head predicate of the composed clause
     * @param args the body predicates in the resulting clause
     * @return a test String representing the composed Prolog clause
     */
    private static String clause(final String head, final String... args) {
        final String sign = " :- ";
        String body = EMPTY;
        for (final String b : args) {
            if (!body.isEmpty()) {
                body += COMMA;
            }
            body += b;
        }
        return fact(head + sign + body);
    }

    /**
     * Performs setup for the following tests.
     *
     * @throws IOException if reading resources fails
     * @throws MalformedEplFileException if the input file does not satisfy the EPL format
     */
    @Before
    public void setup() throws IOException, MalformedEplFileException {
        final ExtendedPrologParser parser = new SimpleExtendedPrologParser();
        this.framework = parser.parseFramework(new File(FRAMEWORK_PATH), false);

        this.generator = new TestDataGenerator(this.framework);
    }

    /**
     * The SimplePrologCompositionAnalyzer is considered to be correct and
     * is thus used as a baseline for all other implementations of
     * CompositionAnalyzer.
     * @throws IOException if io fails
     * @throws ExternalSoftwareUnavailableException if JPL is unavailable
     */
    @Test
    public void testAccordanceWithSpca() throws IOException, ExternalSoftwareUnavailableException {
        LOGGER.info("testAccordanceWithSCPA()");
        final SimplePrologCompositionAnalyzer spca = new SimplePrologCompositionAnalyzer(
                this.framework);
        final CompositionAnalyzer self = this.createInstance();

        final int runs = 100;
        final int timeout = 10;

        spca.setTimeout(timeout);
        self.setTimeout(timeout);

        int conflicts = 0;
        int errors = 0;

        for (int i = 0; i < runs; i++) {
            final int amount = (int) (3 * Math.random()) + 1;

            final List<Property> properties = this.generator
                    .getRandomComposableModuleProperties(amount);

            final SearchResult<DecompositionTree> trustedResult = spca
                    .generateComposition(properties);
            final SearchResult<DecompositionTree> result = self.generateComposition(properties);

            if (result.getState() == QueryState.ERROR) {
                errors++;
            }

            if (trustedResult.getState() == QueryState.FAILED) {
                if (result.getState() == QueryState.SUCCESS) {
                    conflicts++;
                }
            }

            if (trustedResult.getState() == QueryState.SUCCESS) {
                if (result.getState() == QueryState.FAILED) {
                    conflicts++;
                }
            }
        }

        if (errors > 0 || conflicts > 0) {
            fail();
        }
    }

    /**
     * Tests random property sets.
     * @throws IOException if io fails
     * @throws ExternalSoftwareUnavailableException if external software is unavailable
     */
    @Test
    public void testRandomPropertySets() throws IOException, ExternalSoftwareUnavailableException {
        LOGGER.info("testRandomPropertySets()");
        final int runs = 100;
        final int timeout = 10;

        int success = 0;
        int timeouts = 0;
        int failure = 0;
        int error = 0;

        final CompositionAnalyzer analyzer = this.createInstance();
        analyzer.setTimeout(timeout);

        for (int i = 0; i < runs; i++) {
            final int amount = (int) (5 * Math.random()) + 1;

            final List<Property> properties = this.generator
                    .getRandomComposableModuleProperties(amount);

            LOGGER.debug("Query: " + StringUtils.printCollection(properties));

            final SearchResult<DecompositionTree> result = analyzer.generateComposition(properties);

            if (result.hasValue()) {
                success++;
                LOGGER.debug("Result: " + result.getValue().toString());
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

    /**
     * Tests SMC proof.
     * @throws Exception if something goes wrong
     */
    @Test
    public void testSequentialMajorityComparison() throws Exception {
        LOGGER.info("testSequentialMajorityComparison()");
        final String smc =
            predicate(SEQ_COMP,
                      predicate(LOOP_COMP,
                                predicate(PAR_COMP,
                                          predicate(SEQ_COMP,
                                                    predicate(PASS, TWO, ANY),
                                                    predicate(SEQ_COMP,
                                                              predicate(REV_COMP, PLURALITY),
                                                              predicate(PASS, ONE, ANY))),
                                          predicate(DROP, TWO, ANY),
                                          MAX_AGG),
                                predicate(DEF_EQ_COND, ONE)),
                      ELECT);

        final DecompositionTree smcTree = DecompositionTree.parseString(smc);

        final CompositionAnalyzer analyzer = this.createInstance();
        analyzer.setTimeout(DEFAULT_TIMEOUT);

        final List<Property> properties = new LinkedList<Property>();
        properties.add(this.framework.getProperty(MONO));

        final List<SearchResult<BooleanWithUncertainty>> resultList = analyzer
                .analyzeComposition(smcTree, properties);
        final SearchResult<BooleanWithUncertainty> result = resultList.get(0);

        if (result.getState() == QueryState.TIMEOUT) {
            LOGGER.warn("The current CompositionAnalyzer is very slow. "
                    + "This is not an error by definition, but something" + "seems to be wrong.");
        }

        assertTrue(result.hasValue());
        assertTrue(result.getValue() == BooleanWithUncertainty.TRUE);
    }

    /**
     * Tests simple proofs.
     * @throws IOException if io fails
     * @throws ExternalSoftwareUnavailableException if external software is unavailable
     */
    @Test
    public void testSimpleProofs() throws IOException, ExternalSoftwareUnavailableException {
        final List<Property> properties = new LinkedList<Property>();
        properties.add(this.framework.getProperty(MONO));

        final String votingRule = predicate(SEQ_COMP, predicate(PASS, ONE, R), ELECT);

        final CompositionAnalyzer analyzer = this.createInstance();

        final List<CompositionProof> proof = analyzer
                .proveClaims(DecompositionTree.parseString(votingRule), properties);

        // Prolog variable names are not always the same.
        final String proofString = proof.get(0).toString().replaceAll("_[0-9]+", R);

        final String reference =
                ": "
                + predicate(MONO, predicate(SEQ_COMP, predicate(PASS, ONE, R), ELECT))
                + " "
                + "by seq_comp_mono\n"
                + TAB_COLON
                + predicate(DEFER_LIFT_INV, predicate(PASS, ONE, R))
                + " by pass_mod_dl_inv\n"
                + TAB_COLON
                + predicate(NON_ELECTING, predicate(PASS, ONE, R))
                + " by pass_mod_non_electing\n"
                + TAB_COLON
                + predicate(DEFERS, ONE, predicate(PASS, ONE, R))
                + " by pass_one_mod_def_one\n"
                + TAB_COLON
                + predicate(ELECTING, ELECT)
                + " by elect_mod_electing";
        LOGGER.debug(proofString);
        assertTrue(proofString.equals(reference));
    }

    /**
     * Instance creation to allow reuse for all implementations.
     * @return an instance of the respective class
     * @throws IOException if io fails
     * @throws ExternalSoftwareUnavailableException if external software is unavailablw
     */
    protected abstract CompositionAnalyzer createInstance()
            throws IOException, ExternalSoftwareUnavailableException;

    /**
     * Simple getter.
     *
     * @return the framework
     */
    protected FrameworkRepresentation getFramework() {
        return this.framework;
    }

    /**
     * Simple getter.
     * @return the generator
     */
    protected TestDataGenerator getGenerator() {
        return this.generator;
    }
}
