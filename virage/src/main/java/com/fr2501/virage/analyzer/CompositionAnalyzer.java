package com.fr2501.virage.analyzer;

import java.util.List;

import com.fr2501.virage.types.DecompositionTree;
import com.fr2501.virage.types.Property;
import com.fr2501.virage.types.SearchResult;

/**
 * 
 * The interface defining the methods required for analyzing and generating compositions (e.g. voting rules)
 *
 */
public interface CompositionAnalyzer {
	/**
	 * Sets the timeout in milliseconds for the implementations.
	 * @param millis timeout in milliseconds
	 */
	public void setTimeout(long millis);
	
	/**
	 * Checks whether a given composition satisfies the specified property set.
	 * @param composition the composition
	 * @param properties the property set
	 * @return a {@link SearchResult} containing the result
	 */
	public SearchResult<Boolean> analyzeComposition(DecompositionTree composition, List<Property> properties);
	
	/**
	 * Tries to derive a new composition satisfying the specified property set.
	 * @param properties the property set
	 * @return a {@link SearchResult} containing the result
	 */
	public SearchResult<DecompositionTree> generateComposition(List<Property> properties);
}
