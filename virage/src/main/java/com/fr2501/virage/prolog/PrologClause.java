package com.fr2501.virage.prolog;


import java.util.HashSet;
import java.util.Set;

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
	
	public PrologClause(PrologPredicate fact) {
		this.succedent = fact;
		this.antecedents = new HashSet<PrologPredicate>();
	}
	
	private PrologPredicate getSuccedent() {
		return this.succedent;
	}
	private Set<PrologPredicate> getAntecedents() {
		return this.antecedents;
	}
	
	@Override
	public String toString() {
		String res = "";
		
		res += this.succedent.toString();
		res += " :- ";
		int ctr = 0;
		for(PrologPredicate antecedent: antecedents) {
			ctr++;
			res += antecedent.toString();
			
			if(ctr<this.antecedents.size()) {
				res += ",";
			}
		}
		res += ".";
		
		return res;
	}
	
	public boolean equals(PrologClause clause) {
		if(!this.getSuccedent().equals(clause.getSuccedent())) {
			return false;
		}
		
		if(this.getAntecedents().size() != clause.getAntecedents().size()) {
			return false;
		}
		
		for(PrologPredicate antecedent: this.getAntecedents()) {
			boolean found = false;
			
			for(PrologPredicate compAntecedent: clause.getAntecedents()) {
				if(antecedent.equals(compAntecedent)) {
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
