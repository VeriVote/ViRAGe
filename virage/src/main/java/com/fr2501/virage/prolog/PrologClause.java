package com.fr2501.virage.prolog;

import java.util.LinkedList;
import java.util.List;

/**
 * 
 * Represents a single Prolog clause
 *
 */
public class PrologClause {
	private PrologPredicate succedent;
	private List<PrologPredicate> antecedents;
	
	public PrologClause(PrologPredicate succedent, List<PrologPredicate> antecedents) {
		this.succedent = succedent;
		this.antecedents = antecedents;
	}
	
	public PrologClause(PrologPredicate succedent, PrologPredicate antecedent) {
		this.succedent = succedent;
		this.antecedents = new LinkedList<PrologPredicate>();
		this.antecedents.add(antecedent);
	}
	
	/**
	 * Creates a Prolog clause without any antecedents (i.e. a fact).
	 * @param fact the fact
	 */
	public PrologClause(PrologPredicate fact) {
		this.succedent = fact;
		this.antecedents = new LinkedList<PrologPredicate>();
	}
	
	public PrologPredicate getSuccedent() {
		return this.succedent;
	}
	
	public List<PrologPredicate> getAntecedents() {
		return this.antecedents;
	}
	
	/**
	 * Checks, whether a clause is a fact.
	 * @return true if {@code this} is a fact, false otherwise
	 */
	public boolean isAFact() {
		return this.antecedents.isEmpty();
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
		}
		if (succedent == null) {
			if (other.succedent != null)
				return false;
		} else if (!succedent.equals(other.succedent))
			return false;
		
		if(this.antecedents.size() != other.antecedents.size()) {
			return false;
		}
		for(int i=0; i<this.antecedents.size(); i++) {
			if(!this.antecedents.get(i).equals(other.antecedents.get(i))) {
				return false;
			}
		}
		return true;
	}
}
