package edu.kit.kastel.formal.virage.test.unit;

import java.io.File;
import java.util.LinkedList;
import java.util.List;

import org.junit.Before;
import org.junit.Test;

import edu.kit.kastel.formal.util.StringUtils;
import edu.kit.kastel.formal.util.SystemUtils;
import edu.kit.kastel.formal.virage.analyzer.CompositionAnalyzer;
import edu.kit.kastel.formal.virage.analyzer.SimplePrologCompositionAnalyzer;
import edu.kit.kastel.formal.virage.isabelle.IsabelleTheoryGenerator;
import edu.kit.kastel.formal.virage.prolog.ExtendedPrologParser;
import edu.kit.kastel.formal.virage.prolog.PrologParser;
import edu.kit.kastel.formal.virage.prolog.SimpleExtendedPrologParser;
import edu.kit.kastel.formal.virage.types.CompositionProof;
import edu.kit.kastel.formal.virage.types.DecompositionTree;
import edu.kit.kastel.formal.virage.types.FrameworkRepresentation;
import edu.kit.kastel.formal.virage.types.Property;

/**
 * Test suite for {@link IsabelleTheoryGenerator}.
 *
 * @author VeriVote
 */
public final class IsabelleTheoryGeneratorTest {
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
     * Test Prolog predicate name "condorcet_consistency".
     */
    private static final String CONDORCET = "condorcet_consistency";

    /**
     * Test Prolog predicate name "elimination_module".
     */
    private static final String ELIMINATION = "elimination_module";

    /**
     * Test Prolog predicate name "copeland_score".
     */
    private static final String COPELAND = "copeland_score";

    /**
     * Test Prolog predicate name "less".
     */
    private static final String LESS = "less";

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
     * Path to the (E)PL file.
     */
    private static final String PATH = SystemUtils.RESOURCES + "framework" + PrologParser.DOT_PL;

    /**
     * The compositional framework.
     */
    private FrameworkRepresentation framework;

    /**
     * The analyzer.
     */
    private CompositionAnalyzer analyzer;

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
     *
     * @param properties the desired properties
     * @param composition the composition
     */
    protected void proveClaims(final List<Property> properties, final String composition) {
        final List<CompositionProof> proofs =
                this.analyzer.proveClaims(DecompositionTree.parseString(composition), properties);
        final IsabelleTheoryGenerator generator =
                new IsabelleTheoryGenerator(SystemUtils.RESOURCES + "theories/", this.framework);
        generator.generateTheoryFile(composition, proofs);
    }

    /**
     * Tests proof of condorcet_consistency for an elimination module.
     *
     * <b>Notice:</b> Test disabled after introduction of settings.
     */
    public void testCondorcetProof() {
        final List<Property> properties = new LinkedList<Property>();
        properties.add(this.framework.getProperty(CONDORCET));
        this.proveClaims(properties,
                StringUtils.func(SEQ_COMP, StringUtils.func(ELIMINATION, COPELAND, LESS), ELECT));
    }

    /**
     * Simple proof test.
     */
    @Test
    public void testSimpleProof() {
        final List<Property> properties = new LinkedList<Property>();
        properties.add(this.framework.getProperty(ELECTING));
        properties.add(this.framework.getProperty(MONO));
        this.proveClaims(properties,
                StringUtils.func(SEQ_COMP, StringUtils.func(PASS, ONE, ANY), ELECT));
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
