package com.fr2501.virage;

import static org.junit.Assert.assertTrue;

import java.util.LinkedList;
import java.util.List;

import org.junit.Test;

import com.fr2501.virage.types.DecompositionTree;

public class DecompositionTreeTest {
	@Test
	public void TestConstruction() {
		String tree = "root(b(c,d), e, f(g(h,i)))";
		
		DecompositionTree c = new DecompositionTree("c");
		DecompositionTree d = new DecompositionTree("d");
		List<DecompositionTree> cd = new LinkedList<DecompositionTree>();
		cd.add(c); cd.add(d);
		DecompositionTree b = new DecompositionTree("b", cd);
		DecompositionTree e = new DecompositionTree("e");
		DecompositionTree h = new DecompositionTree("h");
		DecompositionTree i = new DecompositionTree("i");
		List<DecompositionTree> hi = new LinkedList<DecompositionTree>();
		hi.add(h); hi.add(i);
		DecompositionTree g = new DecompositionTree("g", hi);
		DecompositionTree f = new DecompositionTree("f", g);
		List<DecompositionTree> bef = new LinkedList<DecompositionTree>();
		bef.add(b); bef.add(e); bef.add(f);
		DecompositionTree root = new DecompositionTree("root", bef);
		
		DecompositionTree res = DecompositionTree.parseString(tree);
	
		assertTrue(root.equals(res));
	}
}
