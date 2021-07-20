package com.fr2501.virage.types;

import java.util.LinkedList;
import java.util.List;

import com.fr2501.util.StringUtils;

/**
 * A component of the modular framework (e.g. composable modules, aggregators ...)
 *
 */
public class Component implements TypedAndParameterized {
    /**
     * The type.
     */
    private final ComponentType type;
    /**
     * The name.
     */
    private final String name;
    /**
     * The list of parameter types.
     */
    private final List<ComponentType> parameters;

    /**
     * Simple constructor for components without parameters.
     *
     * @param type the type
     * @param name the name
     */
    public Component(final ComponentType type, final String name) {
        this(type, name, new LinkedList<ComponentType>());
    }

    /**
     * Simple constructor.
     *
     * @param type the type
     * @param name the name
     * @param parameters the parameters
     */
    public Component(final ComponentType type, final String name,
            final List<ComponentType> parameters) {
        this.type = type;
        this.name = name;
        this.parameters = parameters;
    }

    /**
     * Safe to override.
     * @return the name
     */
    public String getName() {
        return this.name;
    }

    /**
     * Safe to override.
     */
    @Override
    public List<ComponentType> getParameters() {
        return this.parameters;
    }

    /**
     * Safe to override.
     */
    @Override
    public ComponentType getType() {
        return this.type;
    }

    /**
     * Safe to override.
     */
    @Override
    public String toString() {
        final String res = "(" + this.type + ") " + this.name + "("
                + StringUtils.printCollection(this.parameters) + ")";

        return res;
    }

    /**
     * Converts this to a string, omits type signatures of this and its parameters.
     *
     * @return a string representation of this
     */
    public String toStringWithoutTypeSignature() {
        final String res = this.name + "(" + StringUtils.printCollection(this.parameters) + ")";

        return res;
    }
}
