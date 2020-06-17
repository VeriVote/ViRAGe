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
	private int arity;
	private List<ComponentType> parameters;
	
	public Property(String name, List<ComponentType> parameters) {
		this.name = name;
		this.arity = parameters.size();
		this.parameters = parameters;
	}
	
	public String getName() {
		return this.name;
	}
	
	public int getArity() {
		return this.arity;
	}
	
	public String getInstantiatedString(String string) {
		if(this.parameters.size() != 1) {
			throw new IllegalArgumentException();
		}
		
		String res = this.name + "(" + string + ")";
		
		return res;
	}
	
	public String getInstantiatedString(List<String> strings) {
		if(strings.size() != this.parameters.size()) {
			throw new IllegalArgumentException();
		}
		
		String res = this.name + "(" + StringUtils.printCollection(strings) + ")";
		
		return res;
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