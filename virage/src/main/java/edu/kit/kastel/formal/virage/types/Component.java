package edu.kit.kastel.formal.virage.types;

import java.util.LinkedList;
import java.util.List;

import edu.kit.kastel.formal.util.StringUtils;

/**
 * A component of the modular framework (e.g., modules that can be composed, aggregating
 * components, etc.).
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
     *
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
        return StringUtils.parenthesize(this.typeField.toString())
                + StringUtils.SPACE
                + StringUtils.func(this.nameField,
                                   StringUtils.printCollection(this.parametersField));
    }

    /**
     * Converts this to a string, omits type signatures of this and its parameters.
     *
     * @return a string representation of this
     */
    public String toStringWithoutTypeSignature() {
        return StringUtils.func(this.nameField, StringUtils.printCollection(this.parametersField));
    }
}
