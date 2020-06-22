package com.fr2501.virage.analyzer;

import com.fr2501.virage.prolog.PrologPredicate;
import com.fr2501.virage.types.CompositionRule;
import com.fr2501.virage.types.DecompositionTree;

// TODO: Documentation
public class PropertyTreeMatcher {
	/**
	 * Checks whether the predicate is "embeddable" into the tree topologically.
	 * <b>CAUTION:</b> Right now, this decision is made only based on the succedent.
	 * This is sufficient for the current framework state, but it might not be forever.
	 * If this breaks in the future, this is the place to look at.
	 * @param tree the tree
	 * @param predicate the predicate
	 * @return true if the predicate matches the tree, false otherwise
	 */
	public boolean checkTopologicalMatching(DecompositionTree tree, CompositionRule rule) {
		PrologPredicate succedent = rule.getSuccedent();
		
		if(succedent.getArity() == 0) {
			return true;
		}
		
		if(succedent.getArity() != tree.getArity()) {
			return false;
		}
		
		boolean result = true;
		for(int i=0; i<tree.getArity(); i++) {
			result = result && this.checkTopologicalMatching(tree.getChildren().get(i), succedent.getParameters().get(i));
		}
		
		return result;
	}
	
	private boolean checkTopologicalMatching(DecompositionTree tree, PrologPredicate predicate) {
		if(predicate.getArity() == 0) {
			return true;
		}
		
		if(predicate.getArity() != tree.getArity()) {
			return false;
		}
		
		boolean result = true;
		for(int i=0; i<tree.getArity(); i++) {
			result = result && this.checkTopologicalMatching(tree.getChildren().get(i), predicate.getParameters().get(i));
		}
		
		return result;
	}
}
