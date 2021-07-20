package com.fr2501.virage.types;

import java.util.LinkedList;
import java.util.List;

import com.fr2501.util.StringUtils;
import com.fr2501.virage.prolog.PrologPredicate;

/**
 * A class for representing decomposition trees.
 *
 */
public final class DecompositionTree {
    private final String label;
    private final int arity;
    private final List<DecompositionTree> children;

    @Deprecated // This is very easy to confuse with DecompositionTree.parseString.
    // Use DecompositionTree(label, new LinkedList<DecompositionTree>()) instead.
    public DecompositionTree(final String label) {
        this(label, new LinkedList<DecompositionTree>());
    }

    /**
     * Simple constructor for trees with only one child.
     *
     * @param label the label
     * @param child the child
     */
    public DecompositionTree(final String label, final DecompositionTree child) {
        final List<DecompositionTree> children = new LinkedList<DecompositionTree>();
        children.add(child);

        this.label = label;
        this.arity = 1;
        this.children = children;
    }

    /**
     * Simple constructor.
     *
     * @param label the label
     * @param children the children
     */
    public DecompositionTree(final String label, final List<DecompositionTree> children) {
        this.label = label;
        this.arity = children.size();
        this.children = children;
    }

    /**
     * Creates a DecompositionTree object from a string in bracket notation.
     *
     * @param s the string
     *
     * @return a DecompositionTree representing s
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
            res += "(" + StringUtils.printCollection(this.children) + ")";
            return res;
        }
    }

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
                    res += thisComponent.getParameters().get(i).getName() + ",";
                } else {
                    res += currentChild.toStringWithTypesInsteadOfVariables(framework);
                }
            }

            if (res.endsWith(",")) {
                res = res.substring(0, res.length() - 1);
            }

            res += ")";
        }

        return res;
    }
}
