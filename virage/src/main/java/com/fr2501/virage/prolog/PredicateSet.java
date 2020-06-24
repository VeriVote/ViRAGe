package com.fr2501.virage.prolog;

import java.util.HashSet;

import com.fr2501.virage.types.SearchResult;

//TODO Document
//TODO Implement Set?
public class PredicateSet {
	private HashSet<PrologPredicate> predicates;
	private JPLFacade facade;
	// If a set becomes inconsistent once, it is considered inconsistent forever.
	private boolean isConsistent;
	
	public PredicateSet() {
		this.predicates = new HashSet<PrologPredicate>();
		this.facade = new JPLFacade();
		this.isConsistent = true;
	}
	
	public void add(PrologPredicate newPredicate) {
		if(!this.isConsistent) {
			// If the set is already inconsistent nothing else matters.
			this.predicates.add(newPredicate);
		}
		
		// At this point, the set is consistent, i.e. there can be at most one
		// predicate of any given kind.
		for(PrologPredicate predicate: this.predicates) {
			if(predicate.getName().equals(newPredicate.getName())) {
				if(this.checkSubsumption(newPredicate, predicate)) {
					// New predicate would not add new restrictions.
					return;
				} else if(this.checkSubsumption(predicate, newPredicate)) {
					// New predicate makes old one more specific, old one becomes superfluous.
					this.predicates.remove(predicate);
					this.predicates.add(newPredicate);
					return;
				} else {
					// Two predicates of the same type exist, they do not restrict each other,
					// the set has become inconsistent.
					this.isConsistent = false;
					this.predicates.add(predicate);
					return;
				}
			}
		}
		
		// newPredicate is the only one of its kind, can be added without further thought.
		this.predicates.add(newPredicate);
	}
	
	public boolean isSubsumptionalSubset(PredicateSet set) {
		for(PrologPredicate subPredicate: this.predicates) {
			boolean found = false;
			
			for(PrologPredicate predicate: set.predicates) {
				if(predicate.equals(subPredicate) || this.checkSubsumption(predicate, subPredicate)) {
					found = true;
					break;
				}
			}
			
			if(!found) return false;
		}
		
		return true;
	}
	
	private boolean checkSubsumption(PrologPredicate generic, PrologPredicate specific) {
		String query = "subsumes_term(" + generic.toString() + "," + specific.toString() + ")";
		
		// This query should happen very quickly, no timeout needed.
		SearchResult<Boolean> res = this.facade.factQuery(query, 100000);
		
		if(res.hasValue()) {
			try {
				return res.getValue();
			} catch(Exception e) {
				return false;
			}
		} else {
			return false;
		}
	}
}
