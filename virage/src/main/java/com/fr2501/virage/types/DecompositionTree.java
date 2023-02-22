package com.fr2501.virage.types;

import java.util.LinkedList;
import java.util.List;

import com.fr2501.util.StringUtils;
import com.fr2501.virage.prolog.PrologPredicate;

/**
 * A class for representing decomposition trees.
 *
 * @author VeriVote
 */
public final class DecompositionTree {
    /**
     * The label.
     */
    private final String label;
    /**
     * The arity.
     */
    private int arity;
    /**
     * The children.
     */
    private final List<DecompositionTree> children;

    /**
     * Simple constructor.
     * <b>This is very easy to confuse with DecompositionTree.parseString.
     * Use DecompositionTree(label, new LinkedList...) instead.</b>
     * <b>Warning:</b> This was set to deprecated with no explicit justification,
     * maybe handle with care.
     * @param labelValue the label
     */
    public DecompositionTree(final String labelValue) {
        this(labelValue, new LinkedList<DecompositionTree>());
    }

    /**
     * Simple constructor for trees with only one child.
     *
     * @param labelValue the label
     * @param child the child
     */
    public DecompositionTree(final String labelValue, final DecompositionTree child) {
        this.children = new LinkedList<DecompositionTree>();
        this.children.add(child);

        this.label = labelValue;
        this.arity = 1;
    }

    /**
     * Simple constructor.
     *
     * @param labelValue the label
     * @param childrenValue the children
     */
    public DecompositionTree(final String labelValue, final List<DecompositionTree> childrenValue) {
        this.label = labelValue;
        this.arity = childrenValue.size();
        this.children = childrenValue;
    }

    /**
     * Creates a DecompositionTree object from a string in bracket notation.
     *
     * @param passedString the string
     * @return a DecompositionTree representing s
     * @throws IllegalArgumentException if bracket expression is invalid
     */
    public static DecompositionTree parseString(final String passedString) {
        final String s = StringUtils.removeWhitespace(passedString);

        String label = "";
        final List<DecompositionTree> children = new LinkedList<DecompositionTree>();
        String currentChild = "";
        int level = 0;

        for (int i = 0; i < s.length(); i++) {
            final char current = s.charAt(i);

            if (current == '(') {
                level++;
                if (level == 1) {
                    continue;
                }
            } else if (current == ')') {
                level--;
                if (level < 0) {
                    throw new IllegalArgumentException();
                }
                if (level == 0) {
                    continue;
                }
            } else {
                if (level == 0) {
                    label += current;
                } else if (level == 1) {
                    if (current == ',') {
                        children.add(DecompositionTree.parseString(currentChild));
                        currentChild = "";
                        continue;
                    }
                }
            }

            if (level > 0) {
                currentChild += current;
            }
        }

        if (!currentChild.isEmpty()) {
            children.add(DecompositionTree.parseString(currentChild));
        }

        if (level != 0) {
            throw new IllegalArgumentException();
        }

        return new DecompositionTree(label, children);
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
        final DecompositionTree other = (DecompositionTree) obj;
        if (this.arity != other.arity) {
            return false;
        }
        if (this.children == null) {
            if (other.children != null) {
                return false;
            }
        } else {
            for (int i = 0; i < this.arity; i++) {
                if (!this.children.get(i).equals(other.children.get(i))) {
                    return false;
                }
            }
        }

        if (this.label == null) {
            if (other.label != null) {
                return false;
            }
        } else if (!this.label.equals(other.label)) {
            return false;
        }
        return true;
    }

    public int getArity() {
        return this.arity;
    }

    public List<DecompositionTree> getChildren() {
        return this.children;
    }

    public String getLabel() {
        return this.label;
    }

    /**
     * Fills levels of the tree according to arities in framework.
     * @param framework the framework
     * @throws IllegalArgumentException if a level is already too large
     */
    public void fillMissingVariables(final FrameworkRepresentation framework) {
        final Component thisComponent = framework.getComponent(this.label);
        if(PrologPredicate.isVariable(this.label)
                || thisComponent == null && this.children.isEmpty()) {
            return;
        }

        if(thisComponent == null || this.children.size() > thisComponent.getParameters().size()) {
            throw new IllegalArgumentException();
        }

        for(final DecompositionTree child : this.children) {
            child.fillMissingVariables(framework);
        }

        while(this.children.size() != thisComponent.getParameters().size()) {
            this.children.add(new DecompositionTree(PrologPredicate.ANONYMOUS));
            this.arity++;
        }
    }

    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + this.arity;
        result = prime * result + ((this.children == null) ? 0 : this.children.hashCode());
        result = prime * result + ((this.label == null) ? 0 : this.label.hashCode());
        return result;
    }

    @Override
    public String toString() {
        if (this.arity == 0) {
            return this.label;
        } else {
            String res = this.label;
            res += StringUtils.parenthesize(StringUtils.printCollection(this.children));
            return res;
        }
    }

    /**
     * Creates string representation where all variable nodes are replaced by their
     * respective types.
     * @param framework the compositional framework
     * @return the string representation
     */
    public String toStringWithTypesInsteadOfVariables(final FrameworkRepresentation framework) {
        String res = "";

        if (PrologPredicate.isVariable(this.label)) {
            return res;
        } else {
            res += this.label;
        }

        final Component thisComponent = framework.getComponent(this.label);

        if (!this.children.isEmpty()) {
            res += "(";

            for (int i = 0; i < this.children.size(); i++) {
                final DecompositionTree currentChild = this.children.get(i);

                if (PrologPredicate.isVariable(currentChild.getLabel())) {
                    res += thisComponent.getParameters().get(i).getName()
                            + PrologPredicate.SEPARATOR;
                } else {
                    res += currentChild.toStringWithTypesInsteadOfVariables(framework);
                }
            }

            if (res.endsWith(PrologPredicate.SEPARATOR)) {
                res = res.substring(0, res.length() - 1);
            }

            res += ")";
        }

        return res;
    }
}
