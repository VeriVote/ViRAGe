package com.fr2501.virage.isabelle;

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

import com.fr2501.util.StringUtils;
import com.fr2501.virage.types.ComponentType;
import com.fr2501.virage.types.CompositionProof;
import com.fr2501.virage.types.CompositionRule;
import com.fr2501.virage.types.Property;

/**
 * This class is meant to translate a single {@link CompositionProof} to Isabelle syntax.
 *
 * @author VeriVote
 */
public class IsabelleProofGenerator {
    /**
     * The logger.
     */
    private static final Logger LOGGER = LogManager.getLogger(IsabelleProofGenerator.class);
    /**
     * Template for proof generation.
     */
    private static String proofTemplate = "";

    /**
     * True.
     */
    private static final String TRUE = "true";

    /**
     * A default id for proofs and goals, at least for the time being.
     */
    private static final String DEFAULT_ID = "0";

    /**
     * Theorem name variable.
     */
    private final String varTheoremName = "$THEOREM_NAME";
    /**
     * Goal variable.
     */
    private final String varGoal = "$GOAL";
    /**
     * Proof steps variable.
     */
    private final String varProofSteps = "$PROOF_STEPS";
    /**
     * Subgoal ID variable.
     */
    private final String varSubgoalId = "$SUBGOAL_IDS";
    /**
     * Assumptions variable.
     */
    private final String varAssumptions = "$ASSUMPTIONS";

    /**
     * The Isabelle proof step generator associated to this.
     */
    private final IsabelleProofStepGenerator generator;
    /**
     * Functions and definitions from an Isabelle session.
     */
    private final Map<String, String> functionsAndDefinitions;

    /**
     * The parent theory generator.
     */
    private final IsabelleTheoryGenerator parent;

    /**
     * Simple constructor.
     *
     * @param parentValue the corresponding theory generator
     * @param functionsAndDefinitionsValue set of all functions and definitions in parent's session
     */
    public IsabelleProofGenerator(final IsabelleTheoryGenerator parentValue,
            final Map<String, String> functionsAndDefinitionsValue) {
        if (proofTemplate.isEmpty()) {
            final InputStream proofTemplateStream = this.getClass().getClassLoader()
                    .getResourceAsStream("proof.template");
            final StringWriter writer = new StringWriter();
            try {
                IOUtils.copy(proofTemplateStream, writer, StandardCharsets.UTF_8);
            } catch (final IOException e) {
                LOGGER.error("Something went wrong.", e);
                e.printStackTrace();
            }
            proofTemplate = writer.toString();
        }

        this.functionsAndDefinitions = functionsAndDefinitionsValue;
        this.generator = new IsabelleProofStepGenerator(this, this.functionsAndDefinitions);
        this.parent = parentValue;
    }

    /**
     * Every IsabelleProofGenerator is attached to an {@link IsabelleTheoryGenerator}, this method
     * returns it.
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
    public String generateIsabelleProof(final CompositionProof proof) {
        proof.setId(DEFAULT_ID);

        // A bit hacky
        final String[] splits = proof.getGoal().split("\\(");
        final String property = splits[0];

        final String theoremName = IsabelleTheoryGenerator.VAR_MODULE_NAME + "_" + property + ":";
        final String goal = property + " (" + IsabelleTheoryGenerator.VAR_MODULE_NAME
                + StringUtils.SPACE
                + IsabelleTheoryGenerator.VAR_MODULE_PARAMETERS + ")";

        final Set<String> assumptions = new HashSet<String>();
        final StringBuilder proofSteps = new StringBuilder("");
        for (final CompositionProof subgoal : proof.getAllStepsDepthFirst()) {
            if (subgoal.getAllCompositionRules().size() == 1) {
                final CompositionRule rule = subgoal.getAllCompositionRules().iterator().next();

                if (rule.getOrigin().equals("ASSUMPTION")) {
                    final Property p = this.parent.getFramework()
                            .getProperty(rule.getSuccedent().getName());

                    String newAssumptions = StringUtils.ESCAPED_QUOTATION_MARK
                            + rule.getSuccedent().getName()
                            + StringUtils.SPACE;
                    for (final ComponentType child : p.getParameters()) {
                        // Only parameters defined within the module definition can be referenced,
                        // so if
                        // any others
                        // occur, we skip.
                        if (!this.getParent().getTypedVariables().containsKey(child.getName())) {
                            break;
                        }

                        newAssumptions += this.getParent().getTypedVariables().get(child.getName())
                                + StringUtils.SPACE;

                        newAssumptions += "\"";
                        assumptions.add(newAssumptions);
                    }

                    // This is important to not add subgoal-ids of these "virtual" goals.
                    continue;
                }
            }

            proofSteps.append(this.generator.generateIsabelleProofStep(subgoal));
        }

        if (assumptions.isEmpty()) {
            assumptions.add(TRUE);
        }

        final StringBuilder assumptionString = new StringBuilder("");
        for (final String s : assumptions) {
            assumptionString.append(s + "\n\t");
        }

        final String subgoalIds = DEFAULT_ID;

        return this.replaceVariables(theoremName, goal, proofSteps.toString(),
                                     subgoalIds, assumptionString.toString());
    }

    private String replaceVariables(final String theoremName, final String goal,
            final String proofSteps, final String subgoalIds, final String assumptions) {
        String res = proofTemplate;

        res = res.replace(this.varTheoremName, theoremName);
        res = res.replace(this.varGoal, goal);
        res = res.replace(this.varProofSteps, proofSteps);
        res = res.replace(this.varSubgoalId, subgoalIds);
        res = res.replace(this.varAssumptions, assumptions);

        return res;
    }
}
