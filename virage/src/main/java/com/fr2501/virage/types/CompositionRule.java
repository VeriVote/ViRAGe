package com.fr2501.virage.types;

import java.util.HashSet;
import java.util.Set;

import com.fr2501.virage.prolog.PrologClause;
import com.fr2501.virage.prolog.PrologPredicate;

/**
 * 
 * A composition rule stating different kinds of relations between components, compositional structures and properties
 *
 */
public class CompositionRule {
	private String name;
	private String origin;
	private PrologClause clause;
	
	public CompositionRule(String name, String origin, PrologClause clause) {
		this.name = name;
		this.origin = origin;
		this.clause = clause;
	}
	
	public String getName() {
		return this.name;
	}

	public String getOrigin() {
		return this.origin;
	}

	public PrologClause getClause() {
		return this.clause;
	}
	
	public Set<PrologPredicate> getAntecedents() {
		return this.clause.getAntecedents();
	}
	
	public PrologPredicate getSuccedent() {
		return this.clause.getSuccedent();
	}
	
	//TODO Document
	public Property getSuccedentAsProperty(FrameworkRepresentation framework) {
		return framework.getProperty(this.clause.getSuccedent().getName());
	}
	
	//TODO Document
	public Set<Property> getAndecedentsAsProperties(FrameworkRepresentation framework) {
		Set<Property> res = new HashSet<Property>();
		
		for(PrologPredicate predicate: this.clause.getAntecedents()) {
			Property property = framework.getProperty(predicate.getName());
			
			if(property == null) {
				return null;
			} else {
				res.add(property);
			}
		}
		
		return res;
	}
	
	@Override
	public String toString() {
		String res = this.name + ": " + clause.toString() + " (from " + this.origin + ")";
		
		return res;
	}
}
