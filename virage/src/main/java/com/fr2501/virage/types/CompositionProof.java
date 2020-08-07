package com.fr2501.virage.types;

import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

/**
 * 
 * A class representing a proof using a {@link CompositionRule} for each subgoal,
 * thus making the reasoning of the proof transparent.
 *
 */
public class CompositionProof {
	private String goal;
	private List<CompositionProof> subgoals;
	private CompositionRule rule;
	private String id = "";
	
	public CompositionProof(String goal, List<CompositionProof> subgoals, CompositionRule rule) {
		this.goal = goal;
		this.subgoals = subgoals;
		this.rule = rule;
	}
	
	public CompositionProof(String goal, CompositionRule rule) {
		this.goal = goal;
		this.subgoals = new LinkedList<CompositionProof>();
		this.rule = rule;
	}
	
	public String getGoal() {
		return this.goal;
	}
	
	public List<CompositionProof> getSubgoals() {
		return this.subgoals;
	}
	
	public String getId() {
		return this.id;
	}
	
	public void setId(String id) {
		this.id = id;
		
		for(int i=0; i<this.subgoals.size(); i++) {
			this.subgoals.get(i).setId(id + i);
		}
	}
	
	public String getRuleName() {
		return this.rule.getName();
	}
	
	public List<CompositionProof> getAllStepsDepthFirst() {
		List<CompositionProof> res = new LinkedList<CompositionProof>();
		
		for(CompositionProof subgoal: this.subgoals) {
			res.addAll(subgoal.getAllStepsDepthFirst());
		}
		
		res.add(this);
		
		return res;
	}
	
	public Set<CompositionRule> getAllCompositionRules() {
		Set<CompositionRule> res = new HashSet<CompositionRule>();
		res.add(rule);
		
		for(CompositionProof subgoal: this.subgoals) {
			res.addAll(subgoal.getAllCompositionRules());
		}
		
		return res;
	}
	
	public Set<String> getAllOrigins() {
		Set<String> origins = new HashSet<String>();
		
		Set<CompositionRule> allRules = this.getAllCompositionRules();
		for(CompositionRule rule: allRules) {
			origins.add(rule.getOrigin());
		}
		
		return origins;
	}
	
	@Override
	public String toString() {
		return this.toString(0);
	}
	
	private String toString(int n) {
		String res = "";
		
		for(int i=0; i<n; i++) {
			res += "\t";
		}
		
		res += this.id + ": ";
		
		res += this.goal + " by " + this.rule.getName();
		
		for(CompositionProof subgoal: this.subgoals) {
			res += "\n" + subgoal.toString(n+1);
		}
		
		return res;
	}
}
