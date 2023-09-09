package edu.kit.kastel.formal.virage.types;

import java.util.List;

import edu.kit.kastel.formal.util.StringUtils;
import edu.kit.kastel.formal.virage.core.ConfigReader;

/**
 * Represents a property defined in the modular framework.
 *
 * @author VeriVote
 */
public final class Property implements Parameterized {
    /**
     * The name.
     */
    private final String name;

    /**
     * The arity.
     */
    private final int arity;

    /**
     * The types of the parameters.
     */
    private final List<ComponentType> parameters;

    /**
     * Marks whether a property is atomic.
     */
    private boolean isAtomic;

    /**
     * Simple constructor.
     *
     * @param nameValue the name
     * @param parametersValue the parameters
     */
    public Property(final String nameValue, final List<ComponentType> parametersValue) {
        this.name = nameValue;
        this.arity = parametersValue.size();
        this.parameters = parametersValue;

        final List<String> atomicProperties = ConfigReader.getInstance().getAdditionalProperties();
        this.isAtomic = atomicProperties.contains(this.name);
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
        final Property other = (Property) obj;
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
        return true;
    }

    /**
     * Returns the property's arity.
     *
     * @return the property's arity
     */
    public int getArity() {
        return this.arity;
    }

    /**
     * Returns whether the property is atomic.
     *
     * @return whether the property is atomic
     */
    public boolean isAtomic() {
        return this.isAtomic;
    }

    /**
     * Set whether the property is atomic.
     *
     * @param atomic whether the property shall be atomic
     */
    public void setAtomic(final boolean atomic) {
        this.isAtomic = atomic;
    }

    /**
     * Instantiates a property with values in the given order.
     *
     * @param strings the parameters
     * @return the instantiated string
     * @throws IllegalArgumentException if this has a wrong number of parameters
     */
    public String getInstantiatedString(final List<String> strings) {
        if (strings.size() != this.parameters.size()) {
            throw new IllegalArgumentException();
        }
        return this.name + StringUtils.parenthesize(StringUtils.printCollection(strings));
    }

    /**
     * Instantiates a unary property with the given string.
     *
     * @param string the instantiation string
     * @return the instantiated string
     * @throws IllegalArgumentException if this has more than one parameter
     */
    public String getInstantiatedString(final String string) {
        if (this.parameters.size() != 1) {
            throw new IllegalArgumentException();
        }
        return this.name + StringUtils.parenthesize(string);
    }

    /**
     * Instantiates a property with values in the given order, leaving out the property's name.
     *
     * @param strings the parameters
     * @return the instantiated string
     *  @throws IllegalArgumentException if this has more than one parameter
     */
    public String getInstantiatedStringWithoutName(final List<String> strings) {
        if (strings.size() != this.parameters.size()) {
            throw new IllegalArgumentException();
        }
        return StringUtils.parenthesize(StringUtils.printCollection(strings));
    }

    /**
     * Instantiates a unary property with the given string, leaving out the property's name.
     *
     * @param string the instantiation string
     * @return the instantiated string
     * @throws IllegalArgumentException if this has more than one parameter
     */
    public String getInstantiatedStringWithoutName(final String string) {
        if (this.parameters.size() != 1) {
            throw new IllegalArgumentException();
        }
        return StringUtils.parenthesize(string);
    }

    /**
     * Returns the property's name string.
     *
     * @return the name
     */
    public String getName() {
        return this.name;
    }

    @Override
    public List<ComponentType> getParameters() {
        return this.parameters;
    }

    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + this.arity;
        result = prime * result + ((this.name == null) ? 0 : this.name.hashCode());
        return result;
    }

    @Override
    public String toString() {
        return this.name + StringUtils.parenthesize(StringUtils.printCollection(this.parameters));
    }
}
