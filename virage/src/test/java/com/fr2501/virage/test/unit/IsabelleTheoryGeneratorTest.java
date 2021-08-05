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
     * Path to the (E)PL file.
     */
    private static final String PATH = "src/test/resources/framework.pl";
    /**
     * String representation of SMC.
     */
    private static final String SMC = "sequential_composition(loop_composition("
            + "parallel_composition(" + "sequential_composition(pass_module(2,_),"
            + "sequential_composition(revision_composition(plurality),"
            + "pass_module(1,_)))," + "drop_module(2,_)," + "max_aggregator),"
            + "defer_equal_condition(1))," + "elect_module)";
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
     * @param properties the desired properties
     * @param composition the composition
     */
    protected void proveClaims(final List<Property> properties, final String composition) {
        final List<CompositionProof> proofs = this.analyzer
                .proveClaims(DecompositionTree.parseString(composition), properties);

        final IsabelleTheoryGenerator generator = new IsabelleTheoryGenerator(
                "src/test/resources/theories/", this.framework);

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
                "sequential_composition("
                + "elimination_module(copeland_score,max,less), elect_module)");
    }

    /**
     * Simple proof test.
     */
    @Test
    public void testSimpleProof() {
        final List<Property> properties = new LinkedList<Property>();
        properties.add(this.framework.getProperty("electing"));
        properties.add(this.framework.getProperty("monotonicity"));

        this.proveClaims(properties, "sequential_composition(pass_module(1,_),elect_module)");
    }

    /**
     * SMC proof test.
     */
    @Test
    public void testSmcProof() {
        final List<Property> properties = new LinkedList<Property>();
        properties.add(this.framework.getProperty("monotonicity"));
        properties.add(this.framework.getProperty("electing"));

        this.proveClaims(properties, SMC);
    }

    /**
     * Simple proof test.
     */
    @Test
    public void testVerySimpleProof() {
        final List<Property> properties = new LinkedList<Property>();
        properties.add(this.framework.getProperty("electing"));

        this.proveClaims(properties, "elect_module");
    }
}
