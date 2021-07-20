package com.fr2501.virage.types;

import java.util.List;

import com.fr2501.util.StringUtils;

/**
 * A compositional structure for the modular framework.
 *
 */
@Deprecated
public final class CompositionalStructure implements TypedAndParameterized {
    private final String name;
    private final List<ComponentType> parameters;
    private final ComponentType type;

    public CompositionalStructure(final String name, final ComponentType type,
            final List<ComponentType> parameters) {
        this.name = name;
        this.parameters = parameters;
        this.type = type;
    }

    public String getName() {
        return this.name;
    }

    @Override
    public List<ComponentType> getParameters() {
        return this.parameters;
    }

    @Override
    public ComponentType getType() {
        return this.type;
    }

    @Override
    public String toString() {
        final String res = "(" + this.type + ") " + this.name + "("
                + StringUtils.printCollection(this.parameters) + ")";

        return res;
    }
}
