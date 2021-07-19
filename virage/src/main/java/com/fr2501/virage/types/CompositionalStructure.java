package com.fr2501.virage.types;

import com.fr2501.util.StringUtils;
import java.util.List;

/**
 * A compositional structure for the modular framework.
 *
 */
@Deprecated
public class CompositionalStructure implements TypedAndParameterized {
    private String name;
    private List<ComponentType> parameters;
    private ComponentType type;

    public CompositionalStructure(String name, ComponentType type, List<ComponentType> parameters) {
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
    public String toString() {
        String res = "(" + this.type + ") " + this.name + "("
                + StringUtils.printCollection(this.parameters) + ")";

        return res;
    }

    @Override
    public ComponentType getType() {
        return this.type;
    }
}
