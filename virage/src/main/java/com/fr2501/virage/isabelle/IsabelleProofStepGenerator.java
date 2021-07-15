package com.fr2501.virage.isabelle;

import com.fr2501.virage.prolog.PrologParser;
import com.fr2501.virage.prolog.PrologPredicate;
import com.fr2501.virage.prolog.SimplePrologParser;
import com.fr2501.virage.types.CompositionProof;
import com.fr2501.virage.types.CompositionRule;
import java.io.IOException;
import java.io.InputStream;
import java.io.StringWriter;
import java.nio.charset.StandardCharsets;
import java.util.Map;
import java.util.Set;
import org.apache.commons.io.IOUtils;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

/**
 * This class is meant to translate single proof steps into Isabelle syntax.
 *
 */
public class IsabelleProofStepGenerator {
    private static final Logger logger = LogManager.getLogger(IsabelleProofStepGenerator.class);
    private static String PROOF_STEP_TEMPLATE = "";

    private static String VAR_GOAL_ID = "$GOAL_ID";
    private static String VAR_GOAL = "$GOAL";
    private static String VAR_SUBGOAL_IDS = "$SUBGOAL_IDS";
    private static String VAR_RULE = "$RULE";
    private static String VAR_SOLVER = "$SOLVER";

    private Map<String, String> functionsAndDefinitions;
    private PrologParser parser;
    private IsabelleProofGenerator parent;

    /**
     * Simple constructor.
     * 
     * @param parent the corresponding proof generator
     * @param functionsAndDefinitions set of all functions and definitions in parent's session
     */
    public IsabelleProofStepGenerator(IsabelleProofGenerator parent,
            Map<String, String> functionsAndDefinitions) {
        if (PROOF_STEP_TEMPLATE.isEmpty()) {
            InputStream proofStepTemplateStream = this.getClass().getClassLoader()
                    .getResourceAsStream("proof_step.template");
            StringWriter writer = new StringWriter();
            try {
                IOUtils.copy(proofStepTemplateStream, writer, StandardCharsets.UTF_8);
            } catch (IOException e) {
                logger.error("Something went wrong.", e);
                e.printStackTrace();
            }
            PROOF_STEP_TEMPLATE = writer.toString();
        }

        this.functionsAndDefinitions = functionsAndDefinitions;
        this.parser = new SimplePrologParser();
        this.parent = parent;
    }

    /**
     * Translates a single {@link CompositionProof} step to Isabelle syntax.
     * 
     * @param step the proof step
     * @return a String representing the step in Isabelle syntax
     */
    public String generateIsabelleProofStep(CompositionProof step) {
        final String goalId = step.getId();

        PrologPredicate predicate = this.parser.parsePredicate(step.getGoal());
        this.parent.getParent().replacePrologVariables(predicate);
        Map<String, Set<String>> goalMap = IsabelleUtils
                .translatePrologToIsabelle(this.functionsAndDefinitions, predicate.toString());

        if (goalMap.keySet().size() != 1) {
            throw new IllegalArgumentException();
        }
        String goal = "";
        for (String string : goalMap.keySet()) {
            goal = string;
        }

        String subgoalIds = "";
        for (CompositionProof subgoal : step.getSubgoals()) {
            if (subgoal.getAllCompositionRules().size() == 1) {
                CompositionRule rule = subgoal.getAllCompositionRules().iterator().next();

                if (rule.getOrigin().equals("ASSUMPTION")) {
                    continue;
                }
            }

            subgoalIds += subgoal.getId() + " ";
        }

        String rule = step.getRuleName();

        // TODO: Find heuristics to decide which method to use at what point.
        // 'force' looks quite promising, especially since goals are relatively
        // "simple",
        // so it still returns reasonably quickly most of the time and closes (almost)
        // everything.
        // Problem: If it is not successful, query takes forever.
        // PaMpeR?
        String solver = "simp";

        return this.replaceVariables(goalId, goal, subgoalIds, rule, solver);
    }

    private String replaceVariables(String goalId, String goal, String subgoalIds, String rule,
            String solver) {
        String res = PROOF_STEP_TEMPLATE;

        res = res.replace(VAR_GOAL_ID, goalId);
        res = res.replace(VAR_GOAL, goal);
        res = res.replace(VAR_SUBGOAL_IDS, subgoalIds);
        res = res.replace(VAR_RULE, rule);
        res = res.replace(VAR_SOLVER, solver);

        return res;
    }
}
