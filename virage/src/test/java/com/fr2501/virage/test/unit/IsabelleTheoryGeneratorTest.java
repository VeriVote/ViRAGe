package com.fr2501.virage.test.unit;

import java.io.File;
import java.util.LinkedList;
import java.util.List;

import org.junit.Before;
import org.junit.Test;

import com.fr2501.virage.analyzer.CompositionAnalyzer;
import com.fr2501.virage.analyzer.SimplePrologCompositionAnalyzer;
import com.fr2501.virage.isabelle.IsabelleTheoryGenerator;
import com.fr2501.virage.prolog.ExtendedPrologParser;
import com.fr2501.virage.prolog.SimpleExtendedPrologParser;
import com.fr2501.virage.types.CompositionProof;
import com.fr2501.virage.types.DecompositionTree;
import com.fr2501.virage.types.FrameworkRepresentation;
import com.fr2501.virage.types.Property;

/**
 * Test suite for {@link IsabelleTheoryGenerator}.
 *
 * @author VeriVote
 */
public final class IsabelleTheoryGeneratorTest {
    /**
     * Test Prolog predicate name "".
     */
    private static final String EMPTY = "";

    /**
     * Test Prolog predicate name ",".
     */
    private static final String COMMA = ",";

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
     * Path to the resources directory.
     */
    private static final String RSC = "src/test/resources/";

    /**
     * Path to the (E)PL file.
     */
    private static final String PATH = RSC + "framework.pl";

    /**
     * The compositional framework.
     */
    private FrameworkRepresentation framework;

    /**
     * The analyzer.
     */
    private CompositionAnalyzer analyzer;

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
     * Initialization for the following tests.
     *
     * @throws Exception if something goes wrong
     */
    @Before
    public void init() throws Exception {
        final ExtendedPrologParser parser = new SimpleExtendedPrologParser();
        this.framework = parser.parseFramework(new File(PATH), false);

        this.analyzer = new SimplePrologCompositionAnalyzer(this.framework);
    }

    /**
     * Used to prove claims for further test use.
     * @param properties the desired properties
     * @param composition the composition
     */
    protected void proveClaims(final List<Property> properties, final String composition) {
        final List<CompositionProof> proofs = this.analyzer
                .proveClaims(DecompositionTree.parseString(composition), properties);

        final IsabelleTheoryGenerator generator = new IsabelleTheoryGenerator(
                RSC + "theories/", this.framework);

        generator.generateTheoryFile(composition, proofs);
    }

    /*
     * Test disabled after introduction of settings
     *
     * @Test
     */
    /**
     * Tests proof of condorcet_consistency for an elimination module.
     */
    public void testCondorcetProof() {
        final List<Property> properties = new LinkedList<Property>();
        properties.add(this.framework.getProperty("condorcet_consistency"));

        this.proveClaims(properties,
                         predicate(SEQ_COMP,
                                   predicate("elimination_module",
                                             "copeland_score",
                                             "less"),
                                   ELECT));
    }

    /**
     * Simple proof test.
     */
    @Test
    public void testSimpleProof() {
        final List<Property> properties = new LinkedList<Property>();
        properties.add(this.framework.getProperty(ELECTING));
        properties.add(this.framework.getProperty(MONO));

        this.proveClaims(properties, predicate(SEQ_COMP, predicate(PASS, ONE, ANY), ELECT));
    }

    /**
     * SMC proof test.
     */
    @Test
    public void testSmcProof() {
        final List<Property> properties = new LinkedList<Property>();
        properties.add(this.framework.getProperty(MONO));
        properties.add(this.framework.getProperty(ELECTING));

        this.proveClaims(properties, SMC);
    }

    /**
     * Simple proof test.
     */
    @Test
    public void testVerySimpleProof() {
        final List<Property> properties = new LinkedList<Property>();
        properties.add(this.framework.getProperty(ELECTING));

        this.proveClaims(properties, ELECT);
    }
}
