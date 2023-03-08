package edu.kit.kastel.formal.virage.isabelle;

import java.io.IOException;
import java.io.InputStream;
import java.io.StringWriter;
import java.nio.charset.StandardCharsets;
import java.util.Map;
import java.util.Set;

import org.apache.commons.io.IOUtils;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import edu.kit.kastel.formal.virage.prolog.PrologParser;
import edu.kit.kastel.formal.virage.prolog.PrologPredicate;
import edu.kit.kastel.formal.virage.prolog.SimplePrologParser;
import edu.kit.kastel.formal.virage.types.CompositionProof;
import edu.kit.kastel.formal.virage.types.CompositionRule;

/**
 * This class is meant to translate single proof steps into Isabelle syntax.
 *
 * @author VeriVote
 */
public class IsabelleProofStepGenerator {
    /**
     * The logger.
     */
    private static final Logger LOGGER = LogManager.getLogger(IsabelleProofStepGenerator.class);
    /**
     * Template for proof step generation.
     */
    private static String proofStepTemplate = "";

    /**
     * Goal ID variable.
     */
    private static String varGoalId = "$GOAL_ID";
    /**
     * Goal variable.
     */
    private static String varGoal = "$GOAL";
    /**
     * Subgoal ID variable.
     */
    private static String varSubgoalIds = "$SUBGOAL_IDS";
    /**
     * Rule variable.
     */
    private static String varRule = "$RULE";
    /**
     * Solver variable.
     */
    private static String varSolver = "$SOLVER";

    /**
     * Functions and definitions from an Isabelle session.
     */
    private final Map<String, String> functionsAndDefinitions;
    /**
     * The Prolog parser.
     */
    private final PrologParser parser;
    /**
     * The parent Isabelle Proof generator.
     */
    private final IsabelleProofGenerator parent;

    /**
     * Simple constructor.
     *
     * @param parentValue the corresponding proof generator
     * @param functionsAndDefinitionsValue set of all functions and definitions in parent's session
     */
    public IsabelleProofStepGenerator(final IsabelleProofGenerator parentValue,
            final Map<String, String> functionsAndDefinitionsValue) {
        if (proofStepTemplate.isEmpty()) {
            final InputStream proofStepTemplateStream = this.getClass().getClassLoader()
                    .getResourceAsStream("proof_step.template");
            final StringWriter writer = new StringWriter();
            try {
                IOUtils.copy(proofStepTemplateStream, writer, StandardCharsets.UTF_8);
            } catch (final IOException e) {
                LOGGER.error("Something went wrong.", e);
                e.printStackTrace();
            }
            proofStepTemplate = writer.toString();
        }

        this.functionsAndDefinitions = functionsAndDefinitionsValue;
        this.parser = new SimplePrologParser();
        this.parent = parentValue;
    }

    /**
     * Translates a single {@link CompositionProof} step to Isabelle syntax.
     *
     * @param step the proof step
     * @return a String representing the step in Isabelle syntax
     * @throws IllegalArgumentException sometimes
     */
    public String generateIsabelleProofStep(final CompositionProof step) {
        final String goalId = step.getId();

        final PrologPredicate predicate = this.parser.parsePredicate(step.getGoal());
        this.parent.getParent().replacePrologVariables(predicate);
        final Map<String, Set<String>> goalMap = IsabelleUtils
                .translatePrologToIsabelle(this.functionsAndDefinitions, predicate.toString());

        if (goalMap.keySet().size() != 1) {
            throw new IllegalArgumentException();
        }
        String goal = "";
        for (final String string : goalMap.keySet()) {
            goal = string;
        }

        final StringBuilder subgoalIds = new StringBuilder("");
        for (final CompositionProof subgoal : step.getSubgoals()) {
            if (subgoal.getAllCompositionRules().size() == 1) {
                final CompositionRule rule = subgoal.getAllCompositionRules().iterator().next();

                if (rule.getOrigin().equals("ASSUMPTION")) {
                    continue;
                }
            }

            subgoalIds.append(subgoal.getId() + " ");
        }

        final String rule = step.getRuleName();

        // TODO: Find heuristics to decide which method to use at what point.
        // 'force' looks quite promising, especially since goals are relatively
        // "simple",
        // so it still returns reasonably quickly most of the time and closes (almost)
        // everything.
        // Problem: If it is not successful, query takes forever.
        // PaMpeR?
        final String solver = "simp";

        return this.replaceVariables(goalId, goal, subgoalIds.toString(), rule, solver);
    }

    private String replaceVariables(final String goalId, final String goal, final String subgoalIds,
            final String rule, final String solver) {
        String res = proofStepTemplate;

        res = res.replace(varGoalId, goalId);
        res = res.replace(varGoal, goal);
        res = res.replace(varSubgoalIds, subgoalIds);
        res = res.replace(varRule, rule);
        res = res.replace(varSolver, solver);

        return res;
    }
}
