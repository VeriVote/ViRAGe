package com.fr2501.virage.isabelle;

import java.io.File;
import java.io.IOException;
import java.util.Set;

import com.fr2501.util.SimpleFileReader;
import com.fr2501.virage.types.CompositionProof;

//TODO: Document
public class IsabelleProofGenerator {
	private static String PROOF_TEMPLATE = "";
	
	private static String VAR_THEOREM_NAME = "$THEOREM_NAME";
	private static String VAR_GOAL = "$GOAL";
	private static String VAR_PROOF_STEPS = "$PROOF_STEPS";
	private static String VAR_SUBGOAL_IDS = "$SUBGOAL_IDS";
	private static String VAR_MODULE_NAME = "$MODULE_NAME";
	
	private IsabelleProofStepGenerator generator;
	private Set<String> functionsAndDefinitions;
	
	public IsabelleProofGenerator(Set<String> functionsAndDefinitions) {
		if(PROOF_TEMPLATE.equals("")) {
			SimpleFileReader reader = new SimpleFileReader();
			
			String theoryTemplate = this.getClass().getClassLoader().getResource("proof.template").getFile();
			
			try {
				PROOF_TEMPLATE = reader.readFile(new File(theoryTemplate));
			} catch (IOException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
		}
		
		this.functionsAndDefinitions = functionsAndDefinitions;
		this.generator = new IsabelleProofStepGenerator(this.functionsAndDefinitions);
	}
	
	public String generateIsabelleProof(CompositionProof proof, String moduleName) {
		proof.setId("0");
		
		// A bit hacky
		String[] splits = proof.getGoal().split("\\(");
		String property = splits[0];
		
		String theoremName = moduleName + "_" + property + ":";
		String goal = property + " (" + moduleName + ")";
		
		String proofSteps = "";
		for(CompositionProof subgoal: proof.getAllStepsDepthFirst()) {
			proofSteps += this.generator.generateIsabelleProofStep(subgoal);
		}
		
		String subgoalIds = "0";
		
		return this.replaceVariables(theoremName, goal, proofSteps, subgoalIds, moduleName);
	}
	
	private String replaceVariables(String theoremName, String goal, 
			String proofSteps, String subgoalIds, String moduleName) {
		String res = PROOF_TEMPLATE;
		
		res = res.replace(VAR_THEOREM_NAME, theoremName);
		res = res.replace(VAR_GOAL, goal);
		res = res.replace(VAR_PROOF_STEPS, proofSteps);
		res = res.replace(VAR_SUBGOAL_IDS, subgoalIds);
		res = res.replace(VAR_MODULE_NAME, moduleName);
		
		return res;
	}
}
