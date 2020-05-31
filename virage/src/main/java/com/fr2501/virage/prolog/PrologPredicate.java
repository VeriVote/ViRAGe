package com.fr2501.virage.prolog;

import java.util.LinkedList;
import java.util.List;

public class PrologPredicate {
	private String name;
	private List<PrologPredicate> parameters;
	private int arity;
	
	public PrologPredicate(String name, List<PrologPredicate> parameters) {
		this.name = name;
		this.parameters = parameters;
		this.arity = parameters.size();
	}
	
	public PrologPredicate(String name) {
		this.name = name;
		this.parameters = new LinkedList<PrologPredicate>();
		this.arity = 0;
	}
	
	public String getName() {
		return this.name;
	}
	public List<PrologPredicate> getParameters() {
		return this.parameters;
	}
	public int getArity() {
		return this.arity;
	}
	
	@Override
	public String toString() {
		String res = "";
		
		res += this.name;
		if(this.arity > 0) {
			res += "(";
			
			for(int i=0; i<this.arity; i++) {
				res += this.parameters.get(i).toString();
				if(i<this.arity-1) {
					res += ",";
				}
			}
			
			res += ")";
		}
		
		return res;
	}
	
	public boolean equals(PrologPredicate predicate) {
		if(!this.getName().equals(predicate.getName())) {
			return false;
		}
		
		if(this.getArity() != predicate.getArity()) {
			return false;
		}
		
		for(PrologPredicate parameter: this.getParameters()) {
			boolean found = false;
			
			for(PrologPredicate compParameter: predicate.getParameters()) {
				if(parameter.equals(compParameter)) {
					found = true;
				}
			}
			
			if(!found) {
				return false;
			}
		}
		
		return true;
	}
}
