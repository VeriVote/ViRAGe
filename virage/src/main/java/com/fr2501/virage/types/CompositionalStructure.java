package com.fr2501.virage.types;

import java.util.List;

/**
 * 
 * A compositional structure for the modular framework
 *
 */
public class CompositionalStructure implements Parameterized {
	private String name;
	private List<ComponentType> parameters;
	
	public CompositionalStructure(String name, List<ComponentType> parameters) {
		this.name = name;
		this.parameters = parameters;
	}
	
	public String getName() {
		return this.name;
	}
	
	@Override
	public List<ComponentType> getParameters() {
		return this.parameters;
	}
}
