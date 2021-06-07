package com.fr2501.virage.isabelle;

import com.fr2501.virage.types.ComponentType;
import com.fr2501.virage.types.CompositionProof;
import com.fr2501.virage.types.CompositionRule;
import com.fr2501.virage.types.Property;
import java.io.IOException;
import java.io.InputStream;
import java.io.StringWriter;
import java.nio.charset.StandardCharsets;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import org.apache.commons.io.IOUtils;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

/**
 * 
 * This class is meant to translate a single {@link CompositionProof} to
 * Isabelle syntax.
 *
 */
public class IsabelleProofGenerator {
  private static final Logger logger = LogManager.getLogger(IsabelleProofGenerator.class);
  private static String PROOF_TEMPLATE = "";

  private static final String VAR_THEOREM_NAME = "$THEOREM_NAME";
  private static final String VAR_GOAL = "$GOAL";
  private static final String VAR_PROOF_STEPS = "$PROOF_STEPS";
  private static final String VAR_SUBGOAL_IDS = "$SUBGOAL_IDS";
  private static final String VAR_ASSUMPTIONS = "$ASSUMPTIONS";

  private static final String TRUE = "true";

  private IsabelleProofStepGenerator generator;
  private Map<String, String> functionsAndDefinitions;

  private IsabelleTheoryGenerator parent;

  public IsabelleProofGenerator(IsabelleTheoryGenerator parent,
      Map<String, String> functionsAndDefinitions) {
    if (PROOF_TEMPLATE.equals("")) {
      InputStream proofTemplateStream = this.getClass().getClassLoader()
          .getResourceAsStream("proof.template");
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

  /**
   * Every IsabelleProofGenerator is attached to an
   * {@link IsabelleTheoryGenerator}, this method returns it.
   * 
   * @return the parent
   */
  public IsabelleTheoryGenerator getParent() {
    return this.parent;
  }

  /**
   * Translates a {@link CompositionProof} into Isabelle syntax.
   * 
   * @param proof the proof
   * @return a String representing the proof, readable by Isabelle
   */
  public String generateIsabelleProof(CompositionProof proof) {
    proof.setId("0");

    // A bit hacky
    String[] splits = proof.getGoal().split("\\(");
    String property = splits[0];

    String theoremName = IsabelleTheoryGenerator.VAR_MODULE_NAME + "_" + property + ":";
    String goal = property + " (" + IsabelleTheoryGenerator.VAR_MODULE_NAME + " "
        + IsabelleTheoryGenerator.VAR_MODULE_PARAMETERS + ")";

    Set<String> assumptions = new HashSet<String>();
    String proofSteps = "";
    for (CompositionProof subgoal : proof.getAllStepsDepthFirst()) {
      if (subgoal.getAllCompositionRules().size() == 1) {
        CompositionRule rule = subgoal.getAllCompositionRules().iterator().next();

        // TODO Don't just continue, but collect assumptions.
        if (rule.getOrigin().equals("generated")) {
          Property p = this.parent.getFramework().getProperty(rule.getSuccedent().getName());

          String newAssumptions = "\"" + rule.getSuccedent().getName() + " ";
          for (ComponentType child : p.getParameters()) {
            // Only parameters defined within the module definition can be referenced, so if
            // any others
            // occur, we skip.
            if (!this.getParent().getTypedVariables().containsKey(child.getName())) {
              break;
            }

            newAssumptions += this.getParent().getTypedVariables().get(child.getName()) + " ";

            newAssumptions += "\"";
            assumptions.add(newAssumptions);
          }

          // This is important to not add subgoal-ids of these "virtual" goals.
          continue;
        }
      }

      proofSteps += this.generator.generateIsabelleProofStep(subgoal);
    }

    if (assumptions.isEmpty()) {
      assumptions.add(TRUE);
    }

    String assumptionString = "";
    for (String s : assumptions) {
      assumptionString += s + "\n\t";
    }

    String subgoalIds = "0";

    return this.replaceVariables(theoremName, goal, proofSteps, subgoalIds, assumptionString);
  }

  private String replaceVariables(String theoremName, String goal, String proofSteps,
      String subgoalIds,
      String assumptions) {
    String res = PROOF_TEMPLATE;

    res = res.replace(VAR_THEOREM_NAME, theoremName);
    res = res.replace(VAR_GOAL, goal);
    res = res.replace(VAR_PROOF_STEPS, proofSteps);
    res = res.replace(VAR_SUBGOAL_IDS, subgoalIds);
    res = res.replace(VAR_ASSUMPTIONS, assumptions);

    return res;
  }
}
