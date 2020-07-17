package com.fr2501.virage.types;

import java.util.LinkedList;
import java.util.List;

import com.fr2501.virage.prolog.PrologProof;

// TODO Document
public class CompositionProof {
	private String goal;
	private List<CompositionProof> subgoals;
	private CompositionRule rule;
	
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
	
	@Override
	public String toString() {
		return this.toString(0);
	}
	
	private String toString(int n) {
		String res = "";
		
		for(int i=0; i<n; i++) {
			res += "\t";
		}
		
		res += this.goal + " by " + this.rule.getName();
		
		for(CompositionProof subgoal: this.subgoals) {
			res += "\n" + subgoal.toString(n+1);
		}
		
		return res;
	}
}
