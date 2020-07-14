package com.fr2501.virage.jobs;

import java.util.LinkedList;
import java.util.List;

import com.fr2501.virage.core.VirageSearchManager;
import com.fr2501.virage.core.VirageUserInterface;
import com.fr2501.virage.prolog.PrologProof;
import com.fr2501.virage.types.DecompositionTree;
import com.fr2501.virage.types.Property;
import com.fr2501.virage.types.SearchResult;

public class VirageProveJob extends VirageExecutorJobWithFramework<VirageSearchManager, List<List<PrologProof>>> {
	private List<String> propertyStrings;
	private List<Property> properties;
	private DecompositionTree tree;
	
	private List<List<PrologProof>> result;
	
	public VirageProveJob(VirageUserInterface issuer, String tree, List<String> properties) {
		super(issuer);
		
		this.tree = new DecompositionTree(tree);
		this.propertyStrings = properties;
	}
	
	@Override
	public void concreteExecute() {
		this.properties = new LinkedList<Property>();
		
		for(String s: this.propertyStrings) {
			this.properties.add(this.framework.getProperty(s));
		}
		
		this.result = this.executor.proveClaims(tree, properties);
	}

	@Override
	public List<List<PrologProof>> getResult() {
		return this.result;
	}
}
