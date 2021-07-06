package com.fr2501.virage.test.unit;

import static org.junit.Assert.assertTrue;

import com.fr2501.virage.types.DecompositionTree;
import java.util.LinkedList;
import java.util.List;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import org.junit.Test;

/**
 * Test suite for {@link DecompositionTree}.
 *
 */
public class DecompositionTreeTest {
    private static final Logger logger = LogManager.getLogger(DecompositionTreeTest.class);

    @Test
    public void testConstruction() {
        logger.info("testConstruction()");
        final String tree = "root(b(c,d), e, f(g(h,i)))";

        final DecompositionTree c = new DecompositionTree("c");
        final DecompositionTree d = new DecompositionTree("d");
        List<DecompositionTree> cd = new LinkedList<DecompositionTree>();
        cd.add(c);
        cd.add(d);
        final DecompositionTree b = new DecompositionTree("b", cd);
        final DecompositionTree e = new DecompositionTree("e");
        final DecompositionTree h = new DecompositionTree("h");
        final DecompositionTree i = new DecompositionTree("i");
        List<DecompositionTree> hi = new LinkedList<DecompositionTree>();
        hi.add(h);
        hi.add(i);
        DecompositionTree g = new DecompositionTree("g", hi);
        DecompositionTree f = new DecompositionTree("f", g);
        List<DecompositionTree> bef = new LinkedList<DecompositionTree>();
        bef.add(b);
        bef.add(e);
        bef.add(f);
        DecompositionTree root = new DecompositionTree("root", bef);

        DecompositionTree res = DecompositionTree.parseString(tree);

        assertTrue(root.equals(res));
    }
}
