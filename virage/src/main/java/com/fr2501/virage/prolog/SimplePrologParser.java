package com.fr2501.virage.prolog;

import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

public class SimplePrologParser implements PrologParser {
	@Override
	public PrologClause parseSingleClause(String clause) {
		if(clause.equals("")) throw new IllegalArgumentException();
		
		String sanitizedClause = clause.replace(" ", "");
		
		String[] cedents = sanitizedClause.split(":-");
		
		if(cedents.length > 2) {
			throw new IllegalArgumentException();
		}
		
		PrologPredicate succedent = this.breakdownPredicate(cedents[0]);
		if(cedents.length == 1) {
			return new PrologClause(succedent);
		}
		
		String antecedentString = cedents[1];
		Set<PrologPredicate> antecedents;
		antecedents = this.splitAntecedents(antecedentString);
		
		return new PrologClause(succedent, antecedents);
	}
	
	private PrologPredicate breakdownPredicate(String string) {
		if(string.equals("")) throw new IllegalArgumentException();
		String name = "";
		List<PrologPredicate> parameters = new LinkedList<PrologPredicate>();
		String currentPredicate = "";
		int level = 0;
		
		for(int i=0; i<string.length(); i++) {
			char current = string.charAt(i);
			
			if(level == 1) {
				currentPredicate += current;
			}
			
			if(current == '(') {
				level++;
			} else if(current == ')') {
				level--;
				if(level<0) {
					throw new IllegalArgumentException();
				}
			} else if(current == ',' || i == string.length()-1) {
				if(level == 1) {
					parameters.add(this.breakdownPredicate(currentPredicate));
					currentPredicate = "";
				} else if(current != '.'){
					name += current;
				}
			} else if(level == 0) {
				name += current;
			}
		}
		
		if(level != 0) {
			throw new IllegalArgumentException();
		}
		
		return new PrologPredicate(name, parameters);
	}
	
	private Set<PrologPredicate> splitAntecedents(String antecedentString) {
		if(antecedentString.equals("")) throw new IllegalArgumentException();
		Set<PrologPredicate> res = new HashSet<PrologPredicate>();
		String currentPredicate = "";
		int level = 0;
		
		for(int i=0; i<antecedentString.length(); i++) {
			char current = antecedentString.charAt(i);
				
			if(current == '(') {
				level++;
			} else if(current == ')') {
				level--;
				if(level<0) {
					throw new IllegalArgumentException();
				}
			} 
			
			if(level == 0) {
				if(current == ',' || i == antecedentString.length()-1) {
					res.add((this.breakdownPredicate(currentPredicate)));
					currentPredicate = "";
					continue;
				}
			}
			
			currentPredicate += current;
		}
		
		if(level != 0) {
			throw new IllegalArgumentException();
		}
		
		return res;
	}
}
