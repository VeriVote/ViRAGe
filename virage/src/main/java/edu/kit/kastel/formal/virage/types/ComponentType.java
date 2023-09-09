package edu.kit.kastel.formal.virage.types;

/**
 * A type for components of the modular framework.
 *
 * @author VeriVote
 */
public class ComponentType {
    /**
     * The name.
     */
    private final String name;

    /**
     * Simple constructor.
     *
     * @param nameValue the name
     */
    public ComponentType(final String nameValue) {
        this.name = nameValue;
    }

    /**
     * Safe to override.
     */
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
        final ComponentType other = (ComponentType) obj;
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
     * Safe to override.
     *
     * @return the name
     */
    public String getName() {
        return this.name;
    }

    /**
     * Safe to override.
     */
    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + ((this.name == null) ? 0 : this.name.hashCode());
        return result;
    }

    /**
     * Safe to override.
     */
    @Override
    public String toString() {
        return this.name;
    }
}
