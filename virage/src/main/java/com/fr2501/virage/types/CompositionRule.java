package com.fr2501.virage.types;

import java.util.List;

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
	
	public List<PrologPredicate> getAntecedents() {
		return this.clause.getAntecedents();
	}
	
	public PrologPredicate getSuccedent() {
		return this.clause.getSuccedent();
	}
	
	@Override
	public String toString() {
		String res = this.name + ": " + clause.toString() + " (from " + this.origin + ")";
		
		return res;
	}
	
	public String toEPLString() {
		String res = "";
		
		res += "% = " + this.origin + "\n";
		res += "% " + this.name + "\n";
		res += this.clause.toString() + "\n";
		
		return res;
	}
}
