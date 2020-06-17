package com.fr2501.virage.analyzer;

import java.util.Set;

import com.fr2501.virage.types.AnnotatedDecompositionTree;
import com.fr2501.virage.types.DecompositionTree;
import com.fr2501.virage.types.Property;
import com.fr2501.virage.types.SearchResult;

// TODO: Document
public interface CompositionAnalyzer {
	public static long DEFAULT_TIMEOUT = 10000;
	
	public void setTimeout(long millis);
	public SearchResult<Boolean> analyzeComposition(DecompositionTree composition, Set<Property> properties);
	public SearchResult<Set<DecompositionTree>> generateComposition(Set<Property> properties) throws Exception;
}
