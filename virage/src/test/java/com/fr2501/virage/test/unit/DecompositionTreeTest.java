package com.fr2501.virage.test.unit;

import static org.junit.Assert.assertTrue;

import java.util.LinkedList;
import java.util.List;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import org.junit.Test;

import com.fr2501.virage.types.DecompositionTree;

/**
 * Test suite for {@link DecompositionTree}.
 *
 */
public class DecompositionTreeTest {
    /**
     * The logger.
     */
    private static final Logger LOGGER = LogManager.getLogger(DecompositionTreeTest.class);

    /**
     * Simple test.
     */
    @Test
    public void testConstruction() {
        LOGGER.info("testConstruction()");
        final String tree = "root(b(c,d), e, f(g(h,i)))";

        final DecompositionTree c = new DecompositionTree("c");
        final DecompositionTree d = new DecompositionTree("d");
        final List<DecompositionTree> cd = new LinkedList<DecompositionTree>();
        cd.add(c);
        cd.add(d);
        final DecompositionTree b = new DecompositionTree("b", cd);
        final DecompositionTree e = new DecompositionTree("e");
        final DecompositionTree h = new DecompositionTree("h");
        final DecompositionTree i = new DecompositionTree("i");
        final List<DecompositionTree> hi = new LinkedList<DecompositionTree>();
        hi.add(h);
        hi.add(i);
        final DecompositionTree g = new DecompositionTree("g", hi);
        final DecompositionTree f = new DecompositionTree("f", g);
        final List<DecompositionTree> bef = new LinkedList<DecompositionTree>();
        bef.add(b);
        bef.add(e);
        bef.add(f);
        final DecompositionTree root = new DecompositionTree("root", bef);

        final DecompositionTree res = DecompositionTree.parseString(tree);

        assertTrue(root.equals(res));
    }
}
