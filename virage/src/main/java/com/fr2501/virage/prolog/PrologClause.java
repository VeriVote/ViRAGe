package com.fr2501.virage.prolog;

import java.util.HashSet;
import java.util.Set;

/**
 * 
 * Represents a single Prolog clause
 *
 */
public class PrologClause {
	private PrologPredicate succedent;
	private Set<PrologPredicate> antecedents;
	
	public PrologClause(PrologPredicate succedent, Set<PrologPredicate> antecedents) {
		this.succedent = succedent;
		this.antecedents = antecedents;
	}
	
	public PrologClause(PrologPredicate succedent, PrologPredicate antecedent) {
		this.succedent = succedent;
		this.antecedents = new HashSet<PrologPredicate>();
		this.antecedents.add(antecedent);
	}
	
	/**
	 * Creates a Prolog clause without any antecedents (i.e. a fact).
	 * @param fact the fact
	 */
	public PrologClause(PrologPredicate fact) {
		this.succedent = fact;
		this.antecedents = new HashSet<PrologPredicate>();
	}
	
	@Override
	public String toString() {
		String res = "";
		
		res += this.succedent.toString();
		if(!this.antecedents.isEmpty()) {
			res += " :- ";
			int ctr = 0;
			for(PrologPredicate antecedent: antecedents) {
				ctr++;
				res += antecedent.toString();
				
				if(ctr<this.antecedents.size()) {
					res += ",";
				}
			}
		}
		res += ".";
		
		return res;
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((antecedents == null) ? 0 : antecedents.hashCode());
		result = prime * result + ((succedent == null) ? 0 : succedent.hashCode());
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
		PrologClause other = (PrologClause) obj;
		if (antecedents == null) {
			if (other.antecedents != null)
				return false;
		} else if (!antecedents.equals(other.antecedents))
			return false;
		if (succedent == null) {
			if (other.succedent != null)
				return false;
		} else if (!succedent.equals(other.succedent))
			return false;
		return true;
	}
}
