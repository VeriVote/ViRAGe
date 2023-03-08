package edu.kit.kastel.formal.virage.types;

import java.util.List;

import edu.kit.kastel.formal.virage.prolog.PrologClause;
import edu.kit.kastel.formal.virage.prolog.PrologPredicate;

/**
 * A composition rule stating different kinds of relations between components, compositional
 * structures and properties.
 *
 * @author VeriVote
 */
public final class CompositionRule implements Comparable<CompositionRule> {
    /**
     * The name.
     */
    private final String name;
    /**
     * The origin.
     */
    private final String origin;
    /**
     * The Prolog clause.
     */
    private final PrologClause clause;

    /**
     * Simple constructor.
     *
     * @param nameValue the name
     * @param originValue the origin
     * @param clauseValue the clause
     */
    public CompositionRule(final String nameValue, final String originValue,
            final PrologClause clauseValue) {
        this.name = nameValue;
        this.origin = originValue;

        clauseValue.anonymizeSingletons();
        this.clause = clauseValue;
    }

    @Override
    public int compareTo(final CompositionRule rule) {
        if (this.equals(rule)) {
            return 0;
        }

        if (!this.getSuccedent().getName().equals(rule.getSuccedent().getName())) {
            return this.getSuccedent().getName().compareTo(rule.getSuccedent().getName());
        }

        final int toReturn;
        if (this.getAntecedents().size() < rule.getAntecedents().size()) {
            toReturn = -1;
        } else if (this.getAntecedents().size() == rule.getAntecedents().size()) {
            toReturn = 0;
        } else {
            toReturn = 1;
        }

        return toReturn;
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
        final CompositionRule other = (CompositionRule) obj;
        if (this.clause == null) {
            if (other.clause != null) {
                return false;
            }
        } else if (!this.clause.equals(other.clause)) {
            return false;
        }
        if (this.name == null) {
            if (other.name != null) {
                return false;
            }
        } else if (!this.name.equals(other.name)) {
            return false;
        }
        if (this.origin == null) {
            if (other.origin != null) {
                return false;
            }
        } else if (!this.origin.equals(other.origin)) {
            return false;
        }
        return true;
    }

    public List<PrologPredicate> getAntecedents() {
        return this.clause.getAntecedents();
    }

    public PrologClause getClause() {
        return this.clause;
    }

    public String getName() {
        return this.name;
    }

    public String getOrigin() {
        return this.origin;
    }

    public PrologPredicate getSuccedent() {
        return this.clause.getSuccedent();
    }

    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + ((this.clause == null) ? 0 : this.clause.hashCode());
        result = prime * result + ((this.name == null) ? 0 : this.name.hashCode());
        result = prime * result + ((this.origin == null) ? 0 : this.origin.hashCode());
        return result;
    }

    /**
     * Retrieves a representation of this in the EPL format.
     *
     * @return the string representation
     */
    public String toEplString() {
        String res = "";

        res += "% = " + this.origin + System.lineSeparator();
        res += "% " + this.name + System.lineSeparator();
        res += this.clause.toString() + System.lineSeparator();

        return res;
    }

    @Override
    public String toString() {
        final String res = this.name + ": " + this.clause.toString() + " (from " + this.origin
                + ")";

        return res;
    }
}
