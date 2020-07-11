package com.fr2501.virage.jobs;

import java.util.LinkedList;
import java.util.List;

import com.fr2501.virage.core.VirageSearchManager;
import com.fr2501.virage.types.DecompositionTree;
import com.fr2501.virage.types.Property;
import com.fr2501.virage.types.SearchResult;

// TODO: Document
public class VirageGenerateJob extends VirageExecutorJobWithFramework<VirageSearchManager, List<SearchResult<DecompositionTree>>> {
	private List<String> propertyStrings;
	private List<Property> properties;
	
	private List<SearchResult<DecompositionTree>> result;
	
	public VirageGenerateJob(List<String> properties) {
		this.propertyStrings = properties;
	}

	@Override
	public void execute() {
		this.properties = new LinkedList<Property>();
		
		for(String s: this.propertyStrings) {
			this.properties.add(this.framework.getProperty(s));
		}
		
		this.result = this.executor.generateComposition(properties);
		
		this.state = VirageJobState.FINISHED;
	}

	@Override
	public List<SearchResult<DecompositionTree>> getResult() {
		return this.result;
	}
}
