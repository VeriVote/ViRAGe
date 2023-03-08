package edu.kit.kastel.formal.virage.types;

import java.util.List;

import edu.kit.kastel.formal.util.StringUtils;

/**
 * A compositional structure for the modular framework.
 * <b>Warning:</b> This was set to deprecated with no explicit justification,
 * maybe handle with care.
 *
 * @author VeriVote
 */
public final class CompositionalStructure implements TypedAndParameterized {
    /**
     * The name.
     */
    private final String name;
    /**
     * The parameters.
     */
    private final List<ComponentType> parameters;
    /**
     * The type.
     */
    private final ComponentType type;

    /**
     * Simple constructor.
     * @param nameValue the name
     * @param typeValue the type
     * @param parametersValue the parameters
     */
    public CompositionalStructure(final String nameValue, final ComponentType typeValue,
            final List<ComponentType> parametersValue) {
        this.name = nameValue;
        this.parameters = parametersValue;
        this.type = typeValue;
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
        final String res = "(" + this.type + ") " + this.name + StringUtils.parenthesize(
                StringUtils.printCollection(this.parameters));

        return res;
    }
}
