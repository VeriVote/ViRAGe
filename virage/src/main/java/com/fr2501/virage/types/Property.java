package com.fr2501.virage.types;

import java.util.List;

import com.fr2501.util.StringUtils;

/**
 * 
 * Represents a property defined in the modular framework
 *
 */
public class Property implements Parameterized {
	private String name;
	private List<ComponentType> parameters;
	
	public Property(String name, List<ComponentType> parameters) {
		this.name = name;
		this.parameters = parameters;
	}
	
	public String getName() {
		return this.name;
	}
	
	@Override
	public String toString() {
		String res = this.name + "(" + StringUtils.printCollection(this.parameters) + ")";
		
		return res;
	}
	
	@Override
	public List<ComponentType> getParameters() {
		return this.parameters;
	}
}