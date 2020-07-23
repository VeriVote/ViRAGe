package com.fr2501.virage.isabelle;

import java.io.File;
import java.io.IOException;
import java.util.Set;

import com.fr2501.util.SimpleFileReader;
import com.fr2501.virage.types.CompositionProof;

// TODO: Document
public class IsabelleProofStepGenerator {
	private static String PROOF_STEP_TEMPLATE = "";
	
	private static String VAR_GOAL_ID = "$GOAL_ID";
	private static String VAR_GOAL = "$GOAL";
	private static String VAR_SUBGOAL_IDS = "$SUBGOAL_IDS";
	private static String VAR_RULE = "$RULE";
	private static String VAR_SOLVER = "$SOLVER";
	
	private Set<String> functionsAndDefinitions;
	
	public IsabelleProofStepGenerator(Set<String> functionsAndDefinitions) {
		if(PROOF_STEP_TEMPLATE.equals("")) {
			SimpleFileReader reader = new SimpleFileReader();
			
			String theoryTemplate = this.getClass().getClassLoader().getResource("proof_step.template").getFile();
			
			try {
				PROOF_STEP_TEMPLATE = reader.readFile(new File(theoryTemplate));
			} catch (IOException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
		}
		
		this.functionsAndDefinitions = functionsAndDefinitions;
	}
	
	public String generateIsabelleProofStep(CompositionProof step) {
		String goalId = step.getId();
		String goal = IsabelleUtils.translatePrologToIsabelle(this.functionsAndDefinitions, step.getGoal());
		
		String subgoalIds = "";
		for(CompositionProof subgoal: step.getSubgoals()) {
			subgoalIds += subgoal.getId() + " ";
		}
		
		String rule = step.getRuleName();
		
		String solver = "simp";
		
		return this.replaceVariables(goalId, goal, subgoalIds, rule, solver);
	}
	
	private String replaceVariables(String goalId, String goal, String subgoalIds, String rule, String solver) {
		String res = PROOF_STEP_TEMPLATE;
		
		res = res.replace(VAR_GOAL_ID, goalId);
		res = res.replace(VAR_GOAL, goal);
		res = res.replace(VAR_SUBGOAL_IDS, subgoalIds);
		res = res.replace(VAR_RULE, rule);
		res = res.replace(VAR_SOLVER, solver);
		
		return res;
	}
}
