package com.fr2501.virage.analyzer;

import java.util.Set;

import com.fr2501.virage.types.AnnotatedDecompositionTree;
import com.fr2501.virage.types.DecompositionTree;
import com.fr2501.virage.types.Property;

// TODO: Document
public interface CompositionAnalyzer {
	public void setTimeout(long millis);
	public SearchResult analyzeComposition(DecompositionTree composition, Set<Property> properties);
	public SearchResult generateComposition(Set<Property> properties);
}
