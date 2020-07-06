package com.fr2501.virage.core;

import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import com.fr2501.virage.analyzer.CompositionAnalyzer;
import com.fr2501.virage.types.DecompositionTree;
import com.fr2501.virage.types.Property;
import com.fr2501.virage.types.SearchResult;

/**
 * 
 * A class used to enable the use of different solvers without having
 * to change application code.
 *
 */
public class VirageSearchManager {
	private static final Logger logger = LogManager.getLogger(VirageSearchManager.class);
	private List<CompositionAnalyzer> analyzers;
	
	public VirageSearchManager() {
		logger.info("Initialising VirageSearchManager.");
		
		this.analyzers = new LinkedList<CompositionAnalyzer>();
	}
	
	/**
	 * Adds an analyzer to the manager
	 * @param analyzer the analyzer
	 */
	public void addAnalyzer(CompositionAnalyzer analyzer) {
		this.analyzers.add(analyzer);
	}
	
	/**
	 * Calls {@link CompositionAnalyzer#analyzeComposition(DecompositionTree, Set)} on all its analyzers
	 * @param composition the decomposition tree
	 * @param properties the desired property set
	 * @return a list of results, ordered in the same way as the analyzers
	 */
	public List<SearchResult<Boolean>> analyzeComposition(DecompositionTree composition, Set<Property> properties) {
		// TODO Parallelize.
		List<SearchResult<Boolean>> results = new LinkedList<SearchResult<Boolean>>();
		
		for(int i=0; i<this.analyzers.size(); i++) {
			results.add(this.analyzers.get(i).analyzeComposition(composition, properties));
		}
		
		return results;
	}
	
	/**
	 * Calls {@link CompositionAnalyzer#generateComposition(Set)} on all its analyzers
	 * @param properties the desired property set
	 * @return a list of results, ordered in the same way as the analyzers
	 */
	public List<SearchResult<DecompositionTree>> generateComposition(Set<Property> properties) {
		// TODO Parallelize.
		List<SearchResult<DecompositionTree>> results = new LinkedList<SearchResult<DecompositionTree>>();
		
		for(int i=0; i<this.analyzers.size(); i++) {
			results.add(this.analyzers.get(i).generateComposition(properties));
		}
		
		return results;
	}
}