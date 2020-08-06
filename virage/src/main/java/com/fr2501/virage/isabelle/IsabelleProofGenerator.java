package com.fr2501.virage.isabelle;

import java.io.IOException;
import java.io.InputStream;
import java.io.StringWriter;
import java.nio.charset.StandardCharsets;
import java.util.Map;

import org.apache.commons.io.IOUtils;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import com.fr2501.virage.types.CompositionProof;

//TODO: Document
public class IsabelleProofGenerator {
	private static final Logger logger = LogManager.getLogger(IsabelleProofGenerator.class);
	private static String PROOF_TEMPLATE = "";
	
	private static String VAR_THEOREM_NAME = "$THEOREM_NAME";
	private static String VAR_GOAL = "$GOAL";
	private static String VAR_PROOF_STEPS = "$PROOF_STEPS";
	private static String VAR_SUBGOAL_IDS = "$SUBGOAL_IDS";
	
	private IsabelleProofStepGenerator generator;
	private Map<String, String> functionsAndDefinitions;
	
	private IsabelleTheoryGenerator parent;
	
	public IsabelleProofGenerator(IsabelleTheoryGenerator parent, 
			Map<String, String> functionsAndDefinitions) {
		if(PROOF_TEMPLATE.equals("")) {
			InputStream proofTemplateStream = this.getClass().getClassLoader().getResourceAsStream("proof.template");
			StringWriter writer = new StringWriter();
			try {
				IOUtils.copy(proofTemplateStream, writer, StandardCharsets.UTF_8);
			} catch (IOException e) {
				logger.error("Something went wrong.", e);
				e.printStackTrace();
			}
			PROOF_TEMPLATE = writer.toString();
		}
		
		this.functionsAndDefinitions = functionsAndDefinitions;
		this.generator = new IsabelleProofStepGenerator(this, this.functionsAndDefinitions);
		this.parent = parent;
	}
	
	public IsabelleTheoryGenerator getParent() {
		return this.parent;
	}
	
	public String generateIsabelleProof(CompositionProof proof) {
		proof.setId("0");
		
		// A bit hacky
		String[] splits = proof.getGoal().split("\\(");
		String property = splits[0];
		
		String theoremName = IsabelleTheoryGenerator.VAR_MODULE_NAME + "_" + property + ":";
		String goal = property + " (" + IsabelleTheoryGenerator.VAR_MODULE_NAME + " " + IsabelleTheoryGenerator.VAR_MODULE_PARAMETERS + ")";
		
		String proofSteps = "";
		for(CompositionProof subgoal: proof.getAllStepsDepthFirst()) {
			proofSteps += this.generator.generateIsabelleProofStep(subgoal);
		}
		
		String subgoalIds = "0";
		
		return this.replaceVariables(theoremName, goal, proofSteps, subgoalIds);
	}
	
	private String replaceVariables(String theoremName, String goal, 
			String proofSteps, String subgoalIds) {
		String res = PROOF_TEMPLATE;
		
		res = res.replace(VAR_THEOREM_NAME, theoremName);
		res = res.replace(VAR_GOAL, goal);
		res = res.replace(VAR_PROOF_STEPS, proofSteps);
		res = res.replace(VAR_SUBGOAL_IDS, subgoalIds);
		
		return res;
	}
}
