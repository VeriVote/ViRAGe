package com.fr2501.virage.core;

import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import com.fr2501.virage.analyzer.CompositionAnalyzer;
import com.fr2501.virage.prolog.PrologProof;
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
	 * Calls {@link CompositionAnalyzer#analyzeComposition} on all its analyzers
	 * @param composition the decomposition tree
	 * @param properties the desired property set
	 * @return a list of results, ordered in the same way as the analyzers
	 */
	public List<SearchResult<Boolean>> analyzeComposition(DecompositionTree composition, List<Property> properties) {
		// TODO Parallelize.
		List<SearchResult<Boolean>> results = new LinkedList<SearchResult<Boolean>>();
		
		for(int i=0; i<this.analyzers.size(); i++) {
			SearchResult<Boolean> result = this.analyzers.get(i).analyzeComposition(composition, properties);
			results.add(result);
			logger.debug(result);
		}
		
		return results;
	}
	
	// TODO: Document
	public List<List<PrologProof>> proveClaims(DecompositionTree composition, List<Property> properties) {
		// TODO Parallelize.
		List<List<PrologProof>> results = new LinkedList<List<PrologProof>>();
		
		for(int i=0; i<this.analyzers.size(); i++) {
			List<PrologProof>result = this.analyzers.get(i).proveClaims(composition, properties);
			results.add(result);
			logger.debug(result);
		}
		
		return results;
	}
	
	/**
	 * Calls {@link CompositionAnalyzer#generateComposition} on all its analyzers
	 * @param properties the desired property set
	 * @return a list of results, ordered in the same way as the analyzers
	 */
	public List<SearchResult<DecompositionTree>> generateComposition(List<Property> properties) {
		// TODO Parallelize.
		List<SearchResult<DecompositionTree>> results = new LinkedList<SearchResult<DecompositionTree>>();
		
		for(int i=0; i<this.analyzers.size(); i++) {
			SearchResult<DecompositionTree> result = this.analyzers.get(i).generateComposition(properties);
			results.add(result);
			logger.debug(result);
		}
		
		return results;
	}
}
