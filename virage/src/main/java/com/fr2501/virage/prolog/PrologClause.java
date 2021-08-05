package com.fr2501.virage.prolog;

import java.util.LinkedList;
import java.util.List;

/**
 * Represents a single Prolog clause.
 *
 * @author VeriVote
 */
public final class PrologClause {
    /**
     * The succedent.
     */
    private final PrologPredicate succedent;
    /**
     * The antecedent.
     */
    private final List<PrologPredicate> antecedents;

    /**
     * Creates a Prolog clause without any antecedents (i.e. a fact).
     *
     * @param fact the fact
     */
    public PrologClause(final PrologPredicate fact) {
        this.succedent = fact;
        this.antecedents = new LinkedList<PrologPredicate>();
    }

    /**
     * Simple constructor.
     * @param succedentValue the succedent
     * @param antecedentsValue the antecedents
     */
    public PrologClause(final PrologPredicate succedentValue,
            final List<PrologPredicate> antecedentsValue) {
        this.succedent = succedentValue;
        this.antecedents = antecedentsValue;
    }

    /**
     * Simple constructor for clauses with a single antecedent.
     *
     * @param succedentValue the succedent
     * @param antecedentValue the antecedent
     */
    public PrologClause(final PrologPredicate succedentValue,
            final PrologPredicate antecedentValue) {
        this.succedent = succedentValue;
        this.antecedents = new LinkedList<PrologPredicate>();
        this.antecedents.add(antecedentValue);
    }

    /**
     * Replaces singleton variables with '_'.
     */
    public void anonymizeSingletons() {
        final List<PrologPredicate> allPreds = this.succedent.getAllChildren();
        for (final PrologPredicate antecedent : this.antecedents) {
            allPreds.addAll(antecedent.getAllChildren());
        }

        final List<PrologPredicate> allVars = new LinkedList<PrologPredicate>();
        for (final PrologPredicate pred : allPreds) {
            if (pred.isVariable()) {
                allVars.add(pred);
            }
        }

        for (int i = 0; i < allVars.size(); i++) {
            boolean singleton = true;

            for (int j = 0; j < allVars.size() && singleton; j++) {
                if (i == j) {
                    continue;
                }

                if (allVars.get(i).equals(allVars.get(j))) {
                    singleton = false;
                }
            }

            if (singleton) {
                allVars.get(i).setName("_");
            }
        }
    }

    @Override
    public boolean equals(final Object obj) {
        if (this == obj) {
            return true;
        }
        if (obj == null) {
            return false;
        }
        if (this.getClass() != obj.getClass()) {
            return false;
        }
        final PrologClause other = (PrologClause) obj;
        if (this.antecedents == null) {
            if (other.antecedents != null) {
                return false;
            }
        }
        if (this.succedent == null) {
            if (other.succedent != null) {
                return false;
            }
        } else if (!this.succedent.equals(other.succedent)) {
            return false;
        }

        if (this.antecedents.size() != other.antecedents.size()) {
            return false;
        }
        for (int i = 0; i < this.antecedents.size(); i++) {
            if (!this.antecedents.get(i).equals(other.antecedents.get(i))) {
                return false;
            }
        }
        return true;
    }

    public List<PrologPredicate> getAntecedents() {
        return this.antecedents;
    }

    public PrologPredicate getSuccedent() {
        return this.succedent;
    }

    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + ((this.antecedents == null) ? 0 : this.antecedents.hashCode());
        result = prime * result + ((this.succedent == null) ? 0 : this.succedent.hashCode());
        return result;
    }

    /**
     * Checks, whether a clause is a fact.
     *
     * @return true if {@code this} is a fact, false otherwise
     */
    public boolean isFact() {
        return this.antecedents.isEmpty();
    }

    @Override
    public String toString() {
        String res = "";

        res += this.succedent.toString();
        if (!this.antecedents.isEmpty()) {
            res += " :- ";
            int ctr = 0;
            for (final PrologPredicate antecedent : this.antecedents) {
                ctr++;
                res += antecedent.toString();

                if (ctr < this.antecedents.size()) {
                    res += ",";
                }
            }
        }
        res += ".";

        return res;
    }

}
