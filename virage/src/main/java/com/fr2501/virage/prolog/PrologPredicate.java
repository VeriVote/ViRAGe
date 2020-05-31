package com.fr2501.virage.prolog;

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
	
	public String getName() {
		return this.name;
	}
	public List<PrologPredicate> getParameters() {
		return this.parameters;
	}
	
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
}
