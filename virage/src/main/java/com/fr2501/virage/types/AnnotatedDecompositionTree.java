package com.fr2501.virage.types;

import java.util.HashMap;
import java.util.Map;

// TODO: Documentation
public class AnnotatedDecompositionTree {
	private DecompositionTree tree;
	private Map<DecompositionTree, Map<Property, CompositionRule>> annotations;
	
	public AnnotatedDecompositionTree(DecompositionTree tree) {
		this.tree = tree;
		this.annotations = new HashMap<DecompositionTree, Map<Property, CompositionRule>>();
	}
	
	public DecompositionTree getTree() {
		return this.tree;
	}
}
