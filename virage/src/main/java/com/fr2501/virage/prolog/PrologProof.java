package com.fr2501.virage.prolog;

import java.util.LinkedList;
import java.util.List;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import com.fr2501.util.StringUtils;

/**
 * Using the meta interpreter in src/java/main/resources, this class is able to make the Prolog
 * search process more transparent, exposing goals and subgoals for every proof step.
 *
 */
public final class PrologProof {
    private static final Logger logger = LogManager.getLogger(PrologProof.class);

    private static final String SUBGOAL = "subgoal";
    private static final String MORE_GOALS_ON_LEVEL = "','";
    private static final String BRANCH_CLOSE = "true";
    private static final String SEPARATOR = ",";

    private final String goal;
    private final List<PrologProof> subgoals;

    private PrologProof(final String goal) {
        this(goal, new LinkedList<PrologProof>());
    }

    private PrologProof(final String goal, final List<PrologProof> subgoals) {
        this.goal = goal;
        this.subgoals = subgoals;
    }

    /**
     * Translates a String given by the meta interpreter to a PrologProof object.
     *
     * @param string the string
     * @return the PrologProof object
     */
    public static PrologProof createProofFromString(final String string) {
        final String[] splits = string.split(SUBGOAL);
        // First entry of splits is empty, remove it.
        final String[] subgoals = new String[splits.length - 1];
        for (int i = 1; i < splits.length; i++) {
            subgoals[i - 1] = splits[i];
        }

        final boolean[] lastOfLevel = new boolean[subgoals.length];
        final boolean[] closesBranch = new boolean[subgoals.length];

        for (int i = 0; i < subgoals.length; i++) {
            if (i < subgoals.length - 1) {
                lastOfLevel[i + 1] = !subgoals[i].contains(MORE_GOALS_ON_LEVEL);
            }
            // Handle special cases
            if (i == 0 || i == subgoals.length) {
                lastOfLevel[i] = true;
            }

            // A bit of sanitation
            subgoals[i] = subgoals[i].replace(MORE_GOALS_ON_LEVEL, "");
            subgoals[i] = StringUtils.removeWhitespace(subgoals[i]);

            closesBranch[i] = subgoals[i].contains(BRANCH_CLOSE);
            if (closesBranch[i]) {
                // Remove "true" and following brackets, they have served their purpose.
                final String regex = SEPARATOR + BRANCH_CLOSE + ".*";
                subgoals[i] = subgoals[i].replaceAll(regex, "");
            }

            // More sanitation
            if (subgoals[i].startsWith("(")) {
                subgoals[i] = subgoals[i].substring(1, subgoals[i].length());
            }

            if (subgoals[i].endsWith(",(")) {
                subgoals[i] = subgoals[i].substring(0, subgoals[i].length() - 2);
            }

            if (subgoals[i].endsWith(",")) {
                subgoals[i] = subgoals[i].substring(0, subgoals[i].length() - 1);
            }
        }

        final boolean[] closed = new boolean[subgoals.length];
        final int[] levels = new int[subgoals.length];
        int currentLevel = 0;

        for (int i = 0; i < subgoals.length; i++) {
            levels[i] = currentLevel;
            currentLevel++;

            if (closesBranch[i]) {
                // This happens when a statement is the last of its branch,
                // but not its level. Close the corresponding branch and
                // move up one level to continue with the next one.
                if (!lastOfLevel[i]) {
                    closed[i] = true;
                    currentLevel--;
                    continue;
                }

                int j = i;
                while ((lastOfLevel[j] || closed[j]) && j > 0) {
                    closed[j] = true;
                    j--;
                }
                closed[j] = true;

                // j is now the first successor of i, might be i itself,
                // which is not the last of its level. Thus, the next open
                // subgoal has to be on the same level as j.
                currentLevel = levels[j];
            }
        }

        final int[] parents = new int[subgoals.length];
        parents[0] = -1;
        for (int i = 1; i < subgoals.length; i++) {
            final int level = levels[i];

            for (int j = i; j >= 0; j--) {
                if (levels[j] < level) {
                    parents[i] = j;
                    break;
                }
            }
        }

        final PrologProof[] proofs = new PrologProof[subgoals.length];
        for (int i = 0; i < subgoals.length; i++) {
            proofs[i] = new PrologProof(subgoals[i]);
        }
        for (int i = 0; i < subgoals.length; i++) {
            for (int j = 0; j < subgoals.length; j++) {
                if (parents[j] == i) {
                    proofs[i].addSubgoal(proofs[j]);
                }
            }
        }

        final PrologProof res = proofs[0];
        return res;
    }

    private void addSubgoal(final PrologProof subgoal) {
        this.subgoals.add(subgoal);
    }

    public String getGoal() {
        return this.goal;
    }

    public List<PrologProof> getSubgoals() {
        return this.subgoals;
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

        res += this.goal;

        for (final PrologProof subgoal : this.subgoals) {
            res += "\n" + subgoal.toString(n + 1);
        }

        return res;
    }
}
