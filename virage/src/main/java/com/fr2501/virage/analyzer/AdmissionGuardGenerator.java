package com.fr2501.virage.analyzer;

import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import com.fr2501.util.SimpleFileWriter;
import com.fr2501.virage.prolog.PrologClause;
import com.fr2501.virage.prolog.PrologPredicate;
import com.fr2501.virage.types.CompositionRule;
import com.fr2501.virage.types.FrameworkRepresentation;

// TODO: Document
public class AdmissionGuardGenerator {
	private static final String ADMITS = "admits_";
	private static final String SUFFIX = "_wa";
	private static final String ORIGIN = "generated";
	private FrameworkRepresentation framework;
	
	public AdmissionGuardGenerator(FrameworkRepresentation framework) {
		this.framework = framework;
	}
	
	public void createAdmissionGuardFile(String path) {
		List<CompositionRule> newRules = this.generateAdmissionGuards();
		
		// Looks weird, but otherwise CompositionRule.toString() would have to output Prolog source.
		List<PrologClause> newClauses = new LinkedList<PrologClause>();
		for(CompositionRule rule: newRules) {
			newClauses.add(rule.getClause());
		}
		
		SimpleFileWriter writer = new SimpleFileWriter();
		writer.writeCollectionToFile(path, newClauses);
	}
	
	private List<CompositionRule> generateAdmissionGuards() {
		List<CompositionRule> originalRules = framework.getCompositionRules();
		List<CompositionRule> newRules = new LinkedList<CompositionRule>();
			
		// First, generate the rules that introduce the admission guards.
		for(CompositionRule oldRule: originalRules) {
			PrologPredicate succedent = oldRule.getSuccedent();
			
			String newSuccedentName = ADMITS + succedent.getName();
			
			PrologPredicate newSuccedent;
			
			List<PrologPredicate> newAntecedents = new LinkedList<PrologPredicate>();
			
			// Simple implications should keep their antecedents and variables.
			// (Some facts are hit as well, but that does not matter.)
			if(succedent.getDepth() == 1) {
				newSuccedent = new PrologPredicate(newSuccedentName, succedent.getParameters());
				
				for(PrologPredicate antecedent: oldRule.getAntecedents()) {
					String newAntecedentName = ADMITS + antecedent.getName();
					
					newAntecedents.add(new PrologPredicate(newAntecedentName, antecedent.getParameters()));
				}
			} else {
				PrologPredicate anonymizedSuccedent = this.copyAndAnonymizeVariables(succedent);
				newSuccedent = new PrologPredicate(newSuccedentName, anonymizedSuccedent.getParameters());
				
				// newAntecedents stays empty.
			}
			
			PrologClause newClause = new PrologClause(newSuccedent, newAntecedents);
			newRules.add(new CompositionRule("", ORIGIN, newClause));
		}
		
		// Now, alter the old rules to include them.
		for(CompositionRule oldRule: originalRules) {
			String newSuccedentName = oldRule.getSuccedent().getName() + SUFFIX;
			PrologPredicate newSuccedent = new PrologPredicate(newSuccedentName, oldRule.getSuccedent().getParameters());
			
			List<PrologPredicate> newAntecedents = new LinkedList<PrologPredicate>();
			
			for(PrologPredicate antecedent: oldRule.getAntecedents()) {
				PrologPredicate newAntecedent = new PrologPredicate(ADMITS + antecedent.getName(), antecedent.getParameters());
			
				newAntecedents.add(newAntecedent);
			}
			
			for(PrologPredicate antecedent: oldRule.getAntecedents()) {
				PrologPredicate newAntecedent = new PrologPredicate(antecedent.getName() + SUFFIX, antecedent.getParameters());
			
				newAntecedents.add(newAntecedent);
			}
			
			PrologClause newClause = new PrologClause(newSuccedent, newAntecedents);
			
			newRules.add(new CompositionRule("", ORIGIN, newClause));
		}
		
		return newRules;
	}
	
	private PrologPredicate copyAndAnonymizeVariables(PrologPredicate predicate) {
		String newName = "";
		
		if(Character.isUpperCase(predicate.getName().charAt(0))) {
			newName = "_";
		} else {
			newName = predicate.getName();
		}
		
		List<PrologPredicate> newParameters = new LinkedList<PrologPredicate>();
		for(PrologPredicate parameter: predicate.getParameters()) {
			newParameters.add(this.copyAndAnonymizeVariables(parameter));
		}
		
		return new PrologPredicate(newName, newParameters);
	}
}
