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

import com.fr2501.util.Pair;
import com.fr2501.util.StringUtils;
import com.fr2501.virage.analyzer.AdmissionCheckPrologCompositionAnalyzer;
import com.fr2501.virage.analyzer.CompositionAnalyzer;
import com.fr2501.virage.analyzer.SimplePrologCompositionAnalyzer;
import com.fr2501.virage.isabelle.IsabelleProofChecker;
import com.fr2501.virage.isabelle.IsabelleTheoryGenerator;
import com.fr2501.virage.prolog.ExtendedPrologParser;
import com.fr2501.virage.prolog.MalformedEplFileException;
import com.fr2501.virage.prolog.QueryState;
import com.fr2501.virage.prolog.SimpleExtendedPrologParser;
import com.fr2501.virage.types.CompositionProof;
import com.fr2501.virage.types.DecompositionTree;
import com.fr2501.virage.types.ExternalSoftwareUnavailableException;
import com.fr2501.virage.types.FrameworkRepresentation;
import com.fr2501.virage.types.IsabelleBuildFailedException;
import com.fr2501.virage.types.Property;
import com.fr2501.virage.types.SearchResult;

/**
 * Test suite for {@link IsabelleProofChecker}.
 *
 */
public final class IsabelleProofCheckerTest {
    private static final Logger LOGGER = LogManager.getLogger(IsabelleProofCheckerTest.class);

    private static final String EPL_PATH = "src/test/resources/framework.pl";
    private static final String THEORY_PATH = "src/test/resources/old_theories";
    private static final String SMC = "sequential_composition(" + "loop_composition("
            + "parallel_composition(" + "sequential_composition(" + "pass_module(2,_),"
            + "sequential_composition(" + "revision_composition(" + "plurality),"
            + "pass_module(1,_)))," + "drop_module(2,_)," + "max_aggregator),"
            + "defer_equal_condition(1))," + "elect_module)";
    private FrameworkRepresentation framework;
    private CompositionAnalyzer analyzer;
    private IsabelleTheoryGenerator generator;

    private File file;

    /**
     * Initialization for the following tests.
     *
     * @throws IOException if file system interaction fails
     * @throws MalformedEplFileException if the input file does not satisfy the EPL format
     * @throws ExternalSoftwareUnavailableException if Isabelle is unavailable
     */
    @Before
    public void init()
            throws IOException, MalformedEplFileException, ExternalSoftwareUnavailableException {
        final ExtendedPrologParser parser = new SimpleExtendedPrologParser();
        this.framework = parser.parseFramework(new File(EPL_PATH), false);

        this.analyzer = new SimplePrologCompositionAnalyzer(this.framework);
        this.generator = new IsabelleTheoryGenerator(THEORY_PATH, this.framework);
    }

    protected void proveClaims(final List<Property> properties, final String composition) {
        final List<CompositionProof> proofs = this.analyzer
                .proveClaims(DecompositionTree.parseString(composition), properties);

        this.file = this.generator.generateTheoryFile(composition, proofs);
    }

    // Takes long, not performed by default.
    @Test
    public void simpleFrameworkTest() throws IOException, InterruptedException,
        ExternalSoftwareUnavailableException, IsabelleBuildFailedException {
        final List<Property> properties = new LinkedList<Property>();
        properties.add(this.framework.getProperty("electing"));

        this.proveClaims(properties, "elect_module");

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
     * @throws IOException if file operations fail
     * @throws InterruptedException if the process is interrupted
     * @throws ExternalSoftwareUnavailableException
     * @throws IsabelleBuildFailedException
     */
    // @Test
    public void smcTest() throws IOException, InterruptedException,
        ExternalSoftwareUnavailableException, IsabelleBuildFailedException {
        final List<Property> properties = new LinkedList<Property>();
        properties.add(this.framework.getProperty("electing"));
        properties.add(this.framework.getProperty("monotonicity"));

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
        final int _runs = 3;
        final int _timeout = 10;

        int success = 0;
        int timeout = 0;
        int failure = 0;
        int error = 0;

        final CompositionAnalyzer analyzer = new AdmissionCheckPrologCompositionAnalyzer(
                this.framework);
        analyzer.setTimeout(_timeout);

        final IsabelleProofChecker checker = IsabelleProofChecker
                .getInstance(this.framework.getSessionName(), this.framework.getTheoryPath());

        for (int i = 0; i < _runs; i++) {
            final int amount = (int) (5 * Math.random()) + 1;

            final TestDataGenerator generator = new TestDataGenerator(this.framework);
            final List<Property> properties = generator.getRandomComposableModuleProperties(amount);

            LOGGER.debug("Query: " + StringUtils.printCollection(properties));

            final SearchResult<DecompositionTree> result = analyzer.generateComposition(properties);

            if (result.hasValue()) {
                success++;
                LOGGER.debug("Result: " + result.getValue().toString());

                this.proveClaims(properties, result.getValue().toString());
                checker.verifyTheoryFile(this.file, this.framework);
            } else {
                if (result.getState() == QueryState.TIMEOUT) {
                    timeout++;
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
                + timeout + "\nErrors:\t\t" + error);

        if (failure == 100 || success == 100 || timeout == 100) {
            LOGGER.warn("A highly unlikely result occured in the test.\n"
                    + "This might happen by (a very small) chance, so rerunning the test might help.\n"
                    + "If the problem persists, something has gone wrong.");
            fail();
        }
    }
}
