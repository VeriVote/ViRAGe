package com.fr2501.virage.prolog;

import java.util.LinkedList;
import java.util.List;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

/**
 * 
 * A simple implementation of the {@link PrologParser} interface
 *
 */
public class SimplePrologParser implements PrologParser {	
	@Override
	public PrologClause parseSingleClause(String clause) {				
		if(clause.equals("")) throw new IllegalArgumentException();
		
		String sanitizedClause = this.sanitizeClause(clause);		
		if(sanitizedClause.charAt(sanitizedClause.length()-1) != '.') {
			throw new IllegalArgumentException();
		}
		sanitizedClause = sanitizedClause.replace(".", "");
		
		String[] cedents = sanitizedClause.split(":-");
		
		
		if(cedents.length > 2) {
			throw new IllegalArgumentException();
		}
		
		PrologPredicate succedent = this.breakdownPredicate(cedents[0]);
		if(cedents.length == 1) {
			return new PrologClause(succedent);
		}
		
		String antecedentString = cedents[1];
		List<PrologPredicate> antecedents;
		antecedents = this.splitAntecedents(antecedentString);
		
		return new PrologClause(succedent, antecedents);
	}
	
	private String sanitizeClause(String clause) {
		String res = clause.replace(" ", "");
		res = res.replace("\n", "");
		res = res.replace("\t", "");
		
		return res;
	}

	private PrologPredicate breakdownPredicate(String string) {
		if(string.equals("")) throw new IllegalArgumentException();
		String name = "";
		List<PrologPredicate> parameters = new LinkedList<PrologPredicate>();
		String currentPredicate = "";
		int level = 0;
		
		for(int i=0; i<string.length(); i++) {
			char current = string.charAt(i);
			
			if(current == '(') {
				level++;
				if(level == 1) continue;
			} else if(current == ')') {
				level--;
				if(level<0) {
					throw new IllegalArgumentException();
				}
				if(level == 0) continue;
			} else {		
				if(level == 0) {
					name += current;
				} else if(level == 1) {
					if(current == ',') {
						parameters.add(this.breakdownPredicate(currentPredicate));
						currentPredicate = "";
						continue;
					}
				}
			}
				
			if(level>0) {
				currentPredicate += current;
			}
		}
		
		if(!currentPredicate.equals("")) {
			parameters.add(this.breakdownPredicate(currentPredicate));
		}
		
		if(level != 0) {
			throw new IllegalArgumentException();
		}
		
		return new PrologPredicate(name, parameters);
	}
	
	private List<PrologPredicate> splitAntecedents(String antecedentString) {
		if(antecedentString.equals("")) throw new IllegalArgumentException();
		List<PrologPredicate> res = new LinkedList<PrologPredicate>();
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
					if(i == antecedentString.length()-1) {
						currentPredicate += current;
					}
					
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
