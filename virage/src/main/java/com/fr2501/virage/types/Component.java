package com.fr2501.virage.types;

import java.util.LinkedList;
import java.util.List;

import com.fr2501.util.StringUtils;

/**
 * A component of the modular framework (e.g. composable modules, aggregators ...)
 *
 * @author VeriVote
 */
public class Component implements TypedAndParameterized {
    /**
     * The type.
     */
    private final ComponentType typeField;
    /**
     * The name.
     */
    private final String nameField;
    /**
     * The list of parameter types.
     */
    private final List<ComponentType> parametersField;

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
        this.typeField = type;
        this.nameField = name;
        this.parametersField = parameters;
    }

    /**
     * Safe to override.
     * @return the name
     */
    public String getName() {
        return this.nameField;
    }

    /**
     * Safe to override.
     */
    @Override
    public List<ComponentType> getParameters() {
        return this.parametersField;
    }

    /**
     * Safe to override.
     */
    @Override
    public ComponentType getType() {
        return this.typeField;
    }

    /**
     * Safe to override.
     */
    @Override
    public String toString() {
        final String res = StringUtils.parenthesize(this.typeField.toString()) + this.nameField
                + StringUtils.parenthesize(StringUtils.printCollection(this.parametersField));

        return res;
    }

    /**
     * Converts this to a string, omits type signatures of this and its parameters.
     *
     * @return a string representation of this
     */
    public String toStringWithoutTypeSignature() {
        final String res = this.nameField + "("
                + StringUtils.printCollection(this.parametersField) + ")";

        return res;
    }
}
