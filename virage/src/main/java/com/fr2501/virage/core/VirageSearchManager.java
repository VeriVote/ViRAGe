package com.fr2501.virage.core;

import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import com.fr2501.virage.analyzer.CompositionAnalyzer;
import com.fr2501.virage.analyzer.SearchResult;
import com.fr2501.virage.types.DecompositionTree;
import com.fr2501.virage.types.Property;

// TODO: Documentation
public class VirageSearchManager {
	private static final Logger logger = LogManager.getLogger(VirageSearchManager.class);
	private List<CompositionAnalyzer> analyzers;
	
	public VirageSearchManager() {
		logger.info("Initialising VirageSearchManager.");
		
		this.analyzers = new LinkedList<CompositionAnalyzer>();
	}
	
	public void addAnalyzer(CompositionAnalyzer analyzer) {
		this.analyzers.add(analyzer);
	}
	
	public List<SearchResult> analyzeComposition(DecompositionTree composition, Set<Property> properties) {
		// TODO Parallelize.
		List<SearchResult> results = new LinkedList<SearchResult>();
		
		for(int i=0; i<this.analyzers.size(); i++) {
			results.add(this.analyzers.get(i).analyzeComposition(composition, properties));
		}
		
		return results;
	}
	
	public List<SearchResult> generateComposition(Set<Property> properties) {
		// TODO Parallelize.
		List<SearchResult> results = new LinkedList<SearchResult>();
		
		for(int i=0; i<this.analyzers.size(); i++) {
			results.add(this.analyzers.get(i).generateComposition(properties));
		}
		
		return results;
	}
}
