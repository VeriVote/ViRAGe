package com.fr2501.virage.prolog;

import java.util.LinkedList;
import java.util.List;
import java.util.Map;

/**
 * A simple data object to contain a single Prolog predicate and its parameters.
 *
 * @author VeriVote
 */
public final class PrologPredicate {

    /**
     * Name of anonymous variables in Prolog.
     */
    public static final String ANONYMOUS = "_";

    /**
     * Character used to separate children in Strings.
     */
    public static final String SEPARATOR = ",";

    /**
     * The name.
     */
    private String name;
    /**
     * The parameters.
     */
    private final List<PrologPredicate> parameters;
    /**
     * The arity.
     */
    private final int arity;
    /**
     * The depth of this predicate.
     */
    private int depth;

    /**
     * Creates a predicate without any parameters (arity 0).
     *
     * @param nameValue the name of the predicate
     */
    public PrologPredicate(final String nameValue) {
        this.name = nameValue;
        this.parameters = new LinkedList<PrologPredicate>();
        this.arity = 0;
    }

    /**
     * Simple constructor.
     *
     * @param nameValue the name
     * @param parametersValue the parameters
     */
    public PrologPredicate(final String nameValue, final List<PrologPredicate> parametersValue) {
        this.name = nameValue;
        this.parameters = parametersValue;
        this.arity = parametersValue.size();

        this.depth = 0;
        for (final PrologPredicate parameter : this.parameters) {
            if (parameter.depth >= this.depth) {
                this.depth = parameter.depth + 1;
            }
        }
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

    /**
     * Checks whether a PrologPredicate is a variable.
     *
     * @return true if this is a variable, false otherwise
     */
    public boolean isVariable() {
        return PrologPredicate.isVariable(this.name);
    }

    /**
     * Checks whether a string represents a Prolog variable.
     * @param s the string
     * @return true if s is a Prolog variable name, false otherwise
     */
    public static boolean isVariable(final String s) {
        return s.matches("[A-Z_][a-zA-Z_0-9]*");
    }

    public void setName(final String newName) {
        this.name = newName;
    }

    /**
     * Create a deep copy of the given predicate.
     * @param pred the predicate to be copied
     * @return the copy
     */
    public static PrologPredicate copy(final PrologPredicate pred) {
        final String newName = pred.getName();

        final List<PrologPredicate> newChildren = new LinkedList<PrologPredicate>();
        for(final PrologPredicate child: pred.getParameters()) {
            newChildren.add(PrologPredicate.copy(child));
        }

        return new PrologPredicate(newName, newChildren);
    }

    /**
     * Replaces variables in this predicate according to the given map.
     * @param replacements the replacements
     */
    public void replaceVariables(final Map<String, String> replacements) {
        if(replacements.keySet().contains(this.name)) {
            this.name = replacements.get(this.name);
        } else {
            for(final PrologPredicate parameter: this.parameters) {
                parameter.replaceVariables(replacements);
            }
        }
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

    @Override
    public String toString() {
        String res = "";

        res += this.name;
        if (this.arity > 0) {
            res += "(";

            for (int i = 0; i < this.arity; i++) {
                res += this.parameters.get(i).toString();
                if (i < this.arity - 1) {
                    res += SEPARATOR;
                }
            }

            res += ")";
        }

        return res;
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
}
