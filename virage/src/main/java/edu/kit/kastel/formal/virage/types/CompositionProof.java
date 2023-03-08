package edu.kit.kastel.formal.virage.types;

import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

/**
 * A class representing a proof using a {@link CompositionRule} for each subgoal, thus making the
 * reasoning of the proof transparent.
 *
 * @author VeriVote
 */
public final class CompositionProof {
    /**
     * The goal.
     */
    private final String goal;
    /**
     * List of subgoals.
     */
    private final List<CompositionProof> subgoals;
    /**
     * The rule.
     */
    private final CompositionRule rule;
    /**
     * The ID.
     */
    private String id = "";

    /**
     * Simple constructor for a terminal proof step.
     *
     * @param goalValue the goal
     * @param ruleValue the rule
     */
    public CompositionProof(final String goalValue, final CompositionRule ruleValue) {
        this.goal = goalValue;
        this.subgoals = new LinkedList<CompositionProof>();
        this.rule = ruleValue;
    }

    /**
     * Simple constructor.
     *
     * @param goalValue the goal
     * @param subgoalsValue the subgoals
     * @param ruleValue the rule
     */
    public CompositionProof(final String goalValue, final List<CompositionProof> subgoalsValue,
            final CompositionRule ruleValue) {
        this.goal = goalValue;
        this.subgoals = subgoalsValue;
        this.rule = ruleValue;
    }

    /**
     * Retrieves all {@link CompositionRule}s used in the proof.
     *
     * @return the composition rules
     */
    public Set<CompositionRule> getAllCompositionRules() {
        final Set<CompositionRule> res = new HashSet<CompositionRule>();
        res.add(this.rule);

        for (final CompositionProof subgoal : this.subgoals) {
            res.addAll(subgoal.getAllCompositionRules());
        }

        return res;
    }

    /**
     * Returns origins of all rules used in the proof.
     *
     * @return all origins
     */
    public Set<String> getAllOrigins() {
        final Set<String> origins = new HashSet<String>();

        final Set<CompositionRule> allRules = this.getAllCompositionRules();
        for (final CompositionRule localRule : allRules) {
            origins.add(localRule.getOrigin());
        }

        return origins;
    }

    /**
     * Iterates the proof and returns its goals in depth-first order.
     *
     * @return the proof steps in depth-first order
     */
    public List<CompositionProof> getAllStepsDepthFirst() {
        final List<CompositionProof> res = new LinkedList<CompositionProof>();

        for (final CompositionProof subgoal : this.subgoals) {
            res.addAll(subgoal.getAllStepsDepthFirst());
        }

        res.add(this);

        return res;
    }

    public String getGoal() {
        return this.goal;
    }

    public String getId() {
        return this.id;
    }

    public String getRuleName() {
        return this.rule.getName();
    }

    public List<CompositionProof> getSubgoals() {
        return this.subgoals;
    }

    /**
     * Assigns a unique id to each step of the proof.
     *
     * @param newId the id
     */
    public void setId(final String newId) {
        this.id = newId;

        for (int i = 0; i < this.subgoals.size(); i++) {
            this.subgoals.get(i).setId(newId + i);
        }
    }

    @Override
    public String toString() {
        return this.toString(0);
    }

    private String toString(final int n) {
        String res = "";

        for (int i = 0; i < n; i++) {
            res += "\t";
        }

        res += this.id + ": ";

        res += this.goal + " by " + this.rule.getName();

        for (final CompositionProof subgoal : this.subgoals) {
            res += System.lineSeparator() + subgoal.toString(n + 1);
        }

        return res;
    }
}
