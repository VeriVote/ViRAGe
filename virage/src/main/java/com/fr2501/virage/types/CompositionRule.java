package com.fr2501.virage.types;

import java.util.List;

import com.fr2501.virage.prolog.PrologClause;
import com.fr2501.virage.prolog.PrologPredicate;

/**
 * 
 * A composition rule stating different kinds of relations between components, compositional structures and properties
 *
 */
public class CompositionRule implements Comparable<CompositionRule> {
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

	@Override
	public int compareTo(CompositionRule rule) {
		if(this.equals(rule)) return 0;
		
		if(!this.getSuccedent().getName().equals(rule.getSuccedent().getName())) {
			return this.getSuccedent().getName().compareTo(rule.getSuccedent().getName());
		}
		
		if(this.getAntecedents().size() < rule.getAntecedents().size()) {
			return -1;
		} else if (this.getAntecedents().size() == rule.getAntecedents().size()) {
			return 0;
		} else {
			return 1;
		}
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((clause == null) ? 0 : clause.hashCode());
		result = prime * result + ((name == null) ? 0 : name.hashCode());
		result = prime * result + ((origin == null) ? 0 : origin.hashCode());
		return result;
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		CompositionRule other = (CompositionRule) obj;
		if (clause == null) {
			if (other.clause != null)
				return false;
		} else if (!clause.equals(other.clause))
			return false;
		if (name == null) {
			if (other.name != null)
				return false;
		} else if (!name.equals(other.name))
			return false;
		if (origin == null) {
			if (other.origin != null)
				return false;
		} else if (!origin.equals(other.origin))
			return false;
		return true;
	}
}
