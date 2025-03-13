package edu.kit.kastel.formal.virage.isabelle;

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

import edu.kit.kastel.formal.util.StringUtils;
import edu.kit.kastel.formal.virage.prolog.ExtendedPrologStrings;
import edu.kit.kastel.formal.virage.types.ComponentType;
import edu.kit.kastel.formal.virage.types.CompositionProof;
import edu.kit.kastel.formal.virage.types.CompositionRule;
import edu.kit.kastel.formal.virage.types.Property;

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
    private static String proofTemplate = StringUtils.EMPTY;

    /**
     * True.
     */
    private static final String TRUE = "true";

    /**
     * A default id for proofs and goals, at least for the time being.
     */
    private static final String DEFAULT_ID = "0";

    /**
     * File name for the proof template.
     */
    private static final String PROOF_TEMPLATE_FILE_NAME = "proof";

    /**
     * Theorem name variable.
     */
    private static final String VAR_THEOREM_NAME = "$THEOREM_NAME";

    /**
     * Goal variable.
     */
    private static final String VAR_GOAL = "$GOAL";

    /**
     * Proof steps variable.
     */
    private static final String VAR_PROOF_STEPS = "$PROOF_STEPS";

    /**
     * Subgoal ID variable.
     */
    private static final String VAR_SUBGOAL_ID = "$SUBGOAL_IDS";

    /**
     * Assumptions variable.
     */
    private static final String VAR_ASSUMPTIONS = "$ASSUMPTIONS";

    /**
     * The Isabelle proof step generator associated to this.
     */
    private final IsabelleProofStepGenerator generator;

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
        if (IsabelleProofGenerator.proofTemplate.isEmpty()) {
            final InputStream proofTemplateStream =
                    this.getClass().getClassLoader()
                    .getResourceAsStream(PROOF_TEMPLATE_FILE_NAME + IsabelleCodeGenerator.DOT_TMPL);
            final StringWriter writer = new StringWriter();
            try {
                IOUtils.copy(proofTemplateStream, writer, StandardCharsets.UTF_8);
            } catch (final IOException e) {
                LOGGER.error("Something went wrong.", e);
                e.printStackTrace();
            }
            setProofTemplate(writer.toString());
        }
        this.generator = new IsabelleProofStepGenerator(this, functionsAndDefinitionsValue);
        this.parent = parentValue;
    }

    private static synchronized void setProofTemplate(final String newTemplate) {
        proofTemplate = newTemplate;
    }

    private static String replaceVariables(final String theoremName, final String goal,
                                           final String proofSteps, final String subgoalIds,
                                           final String assumptions) {
        return IsabelleProofGenerator.proofTemplate
                .replace(VAR_THEOREM_NAME, theoremName)
                .replace(VAR_GOAL, goal)
                .replace(VAR_PROOF_STEPS, proofSteps)
                .replace(VAR_SUBGOAL_ID, subgoalIds)
                .replace(VAR_ASSUMPTIONS, assumptions);
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
        // A bit of a hack
        final String[] splits = proof.getGoal().split("\\(");
        final String property = splits[0];

        final String theoremName =
                IsabelleTheoryGenerator.VAR_MODULE_NAME + IsabelleTheoryGenerator.NAME_SEPARATOR
                + property + StringUtils.COLON;
        final String goal =
                StringUtils.func2(property,
                        IsabelleTheoryGenerator.VAR_MODULE_NAME,
                        IsabelleTheoryGenerator.VAR_MODULE_PARAMETERS);

        final Set<String> assumptions = new HashSet<String>();
        final StringBuilder proofSteps = new StringBuilder();
        for (final CompositionProof subgoal: proof.getAllStepsDepthFirst()) {
            final Set<CompositionRule> rules = subgoal.getAllCompositionRules();
            if (rules.size() == 1) {
                final CompositionRule rule = rules.iterator().next();
                if (ExtendedPrologStrings.ASSUMPTION.equals(rule.getOrigin())) {
                    final String succName = rule.getSuccedent().getName();
                    final Property p = this.parent.getFramework().getProperty(succName);
                    String newAssumptions = StringUtils.addSpace(StringUtils.QUOTATION + succName);
                    for (final ComponentType child: p.getParameters()) {
                        final String childVar =
                                this.getParent().getTypedVariables().get(child.getName());
                        // Only parameters defined within the module definition can be referenced,
                        // so if
                        // any others
                        // occur, we skip.
                        if (childVar == null) {
                            break;
                        }
                        newAssumptions += StringUtils.addSpace(childVar) + StringUtils.QUOTATION;
                        assumptions.add(newAssumptions);
                    }
                    // This is needed to not add subgoal identities for these "virtual" goals.
                    continue;
                }
            }
            proofSteps.append(this.generator.generateIsabelleProofStep(subgoal));
        }
        if (assumptions.isEmpty()) {
            assumptions.add(TRUE);
        }
        final StringBuilder assumptionString = new StringBuilder();
        for (final String s: assumptions) {
            assumptionString.append(s + System.lineSeparator() + StringUtils.TAB);
        }
        final String subgoalIds = DEFAULT_ID;
        return replaceVariables(theoremName, goal, proofSteps.toString(),
                                subgoalIds, assumptionString.toString());
    }
}
