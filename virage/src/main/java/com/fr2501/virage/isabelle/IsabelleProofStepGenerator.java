package com.fr2501.virage.isabelle;

import java.io.File;
import java.io.IOException;
import java.util.Map;
import java.util.Set;

import com.fr2501.util.SimpleFileReader;
import com.fr2501.virage.prolog.PrologParser;
import com.fr2501.virage.prolog.PrologPredicate;
import com.fr2501.virage.prolog.SimplePrologParser;
import com.fr2501.virage.types.ComponentType;
import com.fr2501.virage.types.CompositionProof;
import com.fr2501.virage.types.FrameworkRepresentation;
import com.fr2501.virage.types.Property;

// TODO: Document
public class IsabelleProofStepGenerator {
	private static String PROOF_STEP_TEMPLATE = "";
	
	private static String VAR_GOAL_ID = "$GOAL_ID";
	private static String VAR_GOAL = "$GOAL";
	private static String VAR_SUBGOAL_IDS = "$SUBGOAL_IDS";
	private static String VAR_RULE = "$RULE";
	private static String VAR_SOLVER = "$SOLVER";
	
	private Map<String, String> functionsAndDefinitions;
	private PrologParser parser;
	private IsabelleProofGenerator parent;
	
	private FrameworkRepresentation framework;
	
	
	public IsabelleProofStepGenerator(FrameworkRepresentation framework,
			IsabelleProofGenerator parent, Map<String, String> functionsAndDefinitions) {
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
		
		this.framework = framework;
		this.functionsAndDefinitions = functionsAndDefinitions;
		this.parser = new SimplePrologParser();
		this.parent = parent;
	}
	
	public String generateIsabelleProofStep(CompositionProof step) {
		String goalId = step.getId();
		
		PrologPredicate predicate = this.parser.parsePredicate(step.getGoal());
		this.parent.getParent().replacePrologVariables(predicate);
		Map<String, Set<String>> goalMap = IsabelleUtils.translatePrologToIsabelle(this.functionsAndDefinitions, predicate.toString());
		
		if(goalMap.keySet().size() != 1) {
			throw new IllegalArgumentException();
		}
		String goal = "";
		for(String string: goalMap.keySet()) {
			goal = string;
		}
		
		String subgoalIds = "";
		for(CompositionProof subgoal: step.getSubgoals()) {
			subgoalIds += subgoal.getId() + " ";
		}
		
		String rule = step.getRuleName();
		
		// TODO: Find heuristics to decide which method to use at what point.
		// 'force' looks quite promising, especially since goals are relatively "simple",
		// so it still returns reasonably quickly and closes (almost) everything.
		// PaMpeR?
		String solver = "force";
		
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
