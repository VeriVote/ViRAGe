package com.fr2501.virage.prolog;

import java.util.LinkedList;
import java.util.List;

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
	
	public String toString() {
		String res = "";
		
		res += this.succedent.toString();
		res += " :- ";
		for(int i=0; i<this.antecedents.size(); i++) {
			res += this.antecedents.get(i).toString();
			
			if(i<this.antecedents.size()-1) {
				res += ",";
			}
		}
		
		return res;
	}
}
