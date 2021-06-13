package com.fr2501.virage.types;

import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

/**
 * A class representing a proof using a {@link CompositionRule} for each
 * subgoal, thus making the reasoning of the proof transparent.
 *
 */
public class CompositionProof {
  private String goal;
  private List<CompositionProof> subgoals;
  private CompositionRule rule;
  private String id = "";

  /**
   * Simple constructor.

   * @param goal the goal
   * @param subgoals the subgoals
   * @param rule the rule
   */
  public CompositionProof(String goal, List<CompositionProof> subgoals, CompositionRule rule) {
    this.goal = goal;
    this.subgoals = subgoals;
    this.rule = rule;
  }

  /**
   * Simple constructor for a terminal proof step.

   * @param goal the goal
   * @param rule the rule
   */
  public CompositionProof(String goal, CompositionRule rule) {
    this.goal = goal;
    this.subgoals = new LinkedList<CompositionProof>();
    this.rule = rule;
  }

  public String getGoal() {
    return this.goal;
  }

  public List<CompositionProof> getSubgoals() {
    return this.subgoals;
  }

  public String getId() {
    return this.id;
  }

  /**
   * Assigns a unique id to each step of the proof.

   * @param id the id
   */
  public void setId(String id) {
    this.id = id;

    for (int i = 0; i < this.subgoals.size(); i++) {
      this.subgoals.get(i).setId(id + i);
    }
  }

  public String getRuleName() {
    return this.rule.getName();
  }

  /**
   * Iterates the proof and returns its goals in depth-first order.

   * @return the proof steps in depth-first order
   */
  public List<CompositionProof> getAllStepsDepthFirst() {
    List<CompositionProof> res = new LinkedList<CompositionProof>();

    for (CompositionProof subgoal : this.subgoals) {
      res.addAll(subgoal.getAllStepsDepthFirst());
    }

    res.add(this);

    return res;
  }

  /**
   * Retrieves all {@link CompositionRule}s used in the proof.

   * @return the composition rules
   */
  public Set<CompositionRule> getAllCompositionRules() {
    Set<CompositionRule> res = new HashSet<CompositionRule>();
    res.add(rule);

    for (CompositionProof subgoal : this.subgoals) {
      res.addAll(subgoal.getAllCompositionRules());
    }

    return res;
  }

  /** 
   * Returns origins of all rules used in the proof.

   * @return all origins
   */
  public Set<String> getAllOrigins() {
    Set<String> origins = new HashSet<String>();

    Set<CompositionRule> allRules = this.getAllCompositionRules();
    for (CompositionRule rule : allRules) {
      origins.add(rule.getOrigin());
    }

    return origins;
  }

  @Override
  public String toString() {
    return this.toString(0);
  }

  private String toString(int n) {
    String res = "";

    for (int i = 0; i < n; i++) {
      res += "\t";
    }

    res += this.id + ": ";

    res += this.goal + " by " + this.rule.getName();

    for (CompositionProof subgoal : this.subgoals) {
      res += "\n" + subgoal.toString(n + 1);
    }

    return res;
  }
}
