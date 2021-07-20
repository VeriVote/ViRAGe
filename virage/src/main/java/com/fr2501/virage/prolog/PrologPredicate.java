package com.fr2501.virage.prolog;

import java.util.LinkedList;
import java.util.List;

/**
 * A simple data object to contain a single Prolog predicate and its parameters.
 *
 */
public final class PrologPredicate {
    private String name;
    private final List<PrologPredicate> parameters;
    private final int arity;
    private int depth;

    /**
     * Creates a predicate without any parameters (arity 0).
     *
     * @param name the name of the predicate
     */
    public PrologPredicate(final String name) {
        this.name = name;
        this.parameters = new LinkedList<PrologPredicate>();
        this.arity = 0;
    }

    /**
     * Simple constructor.
     *
     * @param name the name
     * @param parameters the parameters
     */
    public PrologPredicate(final String name, final List<PrologPredicate> parameters) {
        this.name = name;
        this.parameters = parameters;
        this.arity = parameters.size();

        this.depth = 0;
        for (final PrologPredicate parameter : this.parameters) {
            if (parameter.depth >= this.depth) {
                this.depth = parameter.depth + 1;
            }
        }
    }

    public static boolean isVariable(final String s) {
        return s.matches("[A-Z_][a-zA-Z_0-9]*");
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
        final PrologPredicate other = (PrologPredicate) obj;
        if (this.arity != other.arity) {
            return false;
        }
        if (this.name == null) {
            if (other.name != null) {
                return false;
            }
        } else if (!this.name.equals(other.name)) {
            return false;
        }
        if (this.parameters == null) {
            if (other.parameters != null) {
                return false;
            }
        }

        if (this.parameters.size() != other.parameters.size()) {
            return false;
        }

        for (int i = 0; i < this.parameters.size(); i++) {
            if (!this.parameters.get(i).equals(other.parameters.get(i))) {
                return false;
            }
        }

        return true;
    }

    /**
     * Returns all children of a predicate.
     *
     * @return the children
     */
    public List<PrologPredicate> getAllChildren() {
        final List<PrologPredicate> res = new LinkedList<PrologPredicate>();
        res.add(this);

        for (final PrologPredicate child : this.parameters) {
            res.addAll(child.getAllChildren());
        }

        return res;
    }

    public int getArity() {
        return this.arity;
    }

    public int getDepth() {
        return this.depth;
    }

    public String getName() {
        return this.name;
    }

    public List<PrologPredicate> getParameters() {
        return this.parameters;
    }

    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + this.arity;
        result = prime * result + ((this.name == null) ? 0 : this.name.hashCode());
        result = prime * result + ((this.parameters == null) ? 0 : this.parameters.hashCode());
        return result;
    }

    /**
     * Checks whether a PrologPredicate is a variable.
     *
     * @return true if this is a variable, false otherwise
     */
    public boolean isVariable() {
        return PrologPredicate.isVariable(this.name);
    }

    public void setName(final String name) {
        this.name = name;
    }

    @Override
    public String toString() {
        String res = "";

        res += this.name;
        if (this.arity > 0) {
            res += "(";

            for (int i = 0; i < this.arity; i++) {
                res += this.parameters.get(i).toString();
                if (i < this.arity - 1) {
                    res += ",";
                }
            }

            res += ")";
        }

        return res;
    }
}
