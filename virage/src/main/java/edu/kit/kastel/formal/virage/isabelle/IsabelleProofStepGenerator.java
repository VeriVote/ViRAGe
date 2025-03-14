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

import edu.kit.kastel.formal.util.StringUtils;
import edu.kit.kastel.formal.virage.prolog.ExtendedPrologStrings;
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
     * File name for the proof step template.
     */
    private static final String PROOF_STEP_TEMPLATE_FILE_NAME = "proof_step";

    /**
     * Isabelle's proof method for simplification tactics.
     */
    private static final String SIMP_PROOF_METHOD = "simp";

    /**
     * Goal ID variable.
     */
    private static final String VAR_GOAL_ID = "$GOAL_ID";

    /**
     * Goal variable.
     */
    private static final String VAR_GOAL = "$GOAL";

    /**
     * Subgoal ID variable.
     */
    private static final String VAR_SUBGOAL_IDS = "$SUBGOAL_IDS";

    /**
     * Rule variable.
     */
    private static final String VAR_RULE = "$RULE";

    /**
     * Solver variable.
     */
    private static final String VAR_SOLVER = "$SOLVER";

    /**
     * Template for proof step generation.
     */
    private static String proofStepTemplate = StringUtils.EMPTY;

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
        if (IsabelleProofStepGenerator.proofStepTemplate.isEmpty()) {
            final InputStream proofStepTemplateStream = this.getClass().getClassLoader()
                    .getResourceAsStream(PROOF_STEP_TEMPLATE_FILE_NAME
                                        + IsabelleCodeGenerator.DOT_TMPL);
            final StringWriter writer = new StringWriter();
            try {
                IOUtils.copy(proofStepTemplateStream, writer, StandardCharsets.UTF_8);
            } catch (final IOException e) {
                LOGGER.error("Something went wrong.", e);
                e.printStackTrace();
            }
            setProotStepTemplate(writer.toString());
        }
        this.functionsAndDefinitions = functionsAndDefinitionsValue;
        this.parser = new SimplePrologParser();
        this.parent = parentValue;
    }

    private static synchronized void setProotStepTemplate(final String newTemplate) {
        proofStepTemplate = newTemplate;
    }

    private static String replaceVariables(final String goalId, final String goal,
                                           final String subgoalIds, final String rule,
                                           final String solver) {
        return IsabelleProofStepGenerator.proofStepTemplate
                .replace(VAR_GOAL_ID, goalId)
                .replace(VAR_GOAL, goal)
                .replace(VAR_SUBGOAL_IDS, subgoalIds)
                .replace(VAR_RULE, rule)
                .replace(VAR_SOLVER, solver);
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
        final Map<String, Set<String>> goalMap =
                IsabelleUtils
                .translatePrologToIsabelle(this.functionsAndDefinitions, predicate.toString());
        if (goalMap.size() != 1) {
            throw new IllegalArgumentException();
        }
        String goal = StringUtils.EMPTY;
        for (final String string: goalMap.keySet()) {
            goal = string;
        }

        final StringBuilder subgoalIds = new StringBuilder();
        for (final CompositionProof subgoal: step.getSubgoals()) {
            final Set<CompositionRule> rules = subgoal.getAllCompositionRules();
            if (rules.size() == 1) {
                if (ExtendedPrologStrings.ASSUMPTION.equals(rules.iterator().next().getOrigin())) {
                    continue;
                }
            }
            subgoalIds.append(StringUtils.addSpace(subgoal.getId()));
        }
        final String rule = step.getRuleName();

        // TODO: Find heuristics to decide which method to use at what point.
        // 'force' looks quite promising, especially since goals are relatively
        // "simple",
        // so it still returns reasonably quickly most of the time and closes (almost)
        // everything.
        // Problem: If it is not successful, query takes forever.
        // PaMpeR?
        return replaceVariables(goalId, goal, subgoalIds.toString(), rule, SIMP_PROOF_METHOD);
    }
}
