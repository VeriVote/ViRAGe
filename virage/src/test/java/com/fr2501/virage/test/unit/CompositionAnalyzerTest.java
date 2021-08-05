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
        int improvements = 0;

        int selfTimeout = 0;
        int trustedTimeout = 0;
        int selfSuccess = 0;
        int trustedSuccess = 0;
        int selfFailure = 0;
        int trustedFailure = 0;

        for (int i = 0; i < runs; i++) {
            final int amount = (int) (3 * Math.random()) + 1;

            final List<Property> properties = this.generator
                    .getRandomComposableModuleProperties(amount);

            LOGGER.debug("Query: " + StringUtils.printCollection(properties));

            final SearchResult<DecompositionTree> trustedResult = spca
                    .generateComposition(properties);
            final SearchResult<DecompositionTree> result = self.generateComposition(properties);

            if (result.getState() == QueryState.ERROR) {
                errors++;
            }

            if (trustedResult.getState() == QueryState.FAILED) {
                trustedFailure++;
                if (result.getState() == QueryState.SUCCESS) {
                    conflicts++;
                    selfSuccess++;
                } else {
                    selfFailure++;
                }
            }

            if (trustedResult.getState() == QueryState.SUCCESS) {
                trustedSuccess++;
                if (result.getState() == QueryState.FAILED) {
                    conflicts++;
                    selfFailure++;
                } else {
                    selfSuccess++;
                }
            }

            if (trustedResult.getState() == QueryState.TIMEOUT) {
                trustedTimeout++;
                if (result.getState() == QueryState.SUCCESS) {
                    improvements++;
                    selfSuccess++;
                } else if (result.getState() == QueryState.FAILED) {
                    improvements++;
                    selfFailure++;
                } else {
                    selfTimeout++;
                }
            }

        }

        LOGGER.debug("Errors: " + errors);
        LOGGER.debug("Conflicts: " + conflicts);
        LOGGER.debug("Improvements: " + improvements);

        if (errors > 0 || conflicts > 0) {
            fail();
        } else {
            LOGGER.debug("Trusted:");
            LOGGER.debug("\tTimeouts: " + trustedTimeout);
            LOGGER.debug("\tFailures: " + trustedFailure);
            LOGGER.debug("\tSuccesses: " + trustedSuccess);
            LOGGER.debug("-----");
            LOGGER.debug("Self:");
            LOGGER.debug("\tTimeouts: " + selfTimeout);
            LOGGER.debug("\tFailures: " + selfFailure);
            LOGGER.debug("\tSuccesses: " + selfSuccess);
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
        final String smc = "sequential_composition(loop_composition(" + "parallel_composition("
                + "sequential_composition(" + "pass_module(2,_),sequential_composition("
                + "revision_composition(" + "plurality)," + "pass_module(1,_))),"
                + "drop_module(2,_)," + "max_aggregator)," + "defer_equal_condition(1)),"
                + "elect_module)";

        final DecompositionTree smcTree = DecompositionTree.parseString(smc);

        final CompositionAnalyzer analyzer = this.createInstance();
        analyzer.setTimeout(DEFAULT_TIMEOUT);

        final List<Property> properties = new LinkedList<Property>();
        properties.add(this.framework.getProperty("monotonicity"));

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
        properties.add(this.framework.getProperty("monotonicity"));

        final String votingRule = "sequential_composition(pass_module(1,R),elect_module)";

        final CompositionAnalyzer analyzer = this.createInstance();

        final List<CompositionProof> proof = analyzer
                .proveClaims(DecompositionTree.parseString(votingRule), properties);

        // Prolog variable names are not always the same.
        final String proofString = proof.get(0).toString().replaceAll("_[0-9]+", "R");

        final String reference =
                ": monotonicity(sequential_composition(pass_module(1,R),elect_module)) "
                + "by seq_comp_mono\n"
                + "\t: defer_lift_invariance(pass_module(1,R)) by pass_mod_dl_inv\n"
                + "\t: non_electing(pass_module(1,R)) by pass_mod_non_electing\n"
                + "\t: defers(1,pass_module(1,R)) by pass_one_mod_def_one\n"
                + "\t: electing(elect_module) by elect_mod_electing";
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
