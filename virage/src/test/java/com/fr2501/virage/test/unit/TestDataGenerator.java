package com.fr2501.virage.test.unit;

import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;

import com.fr2501.virage.types.FrameworkRepresentation;
import com.fr2501.virage.types.Property;

/**
 * Creates different kinds of test data.
 *
 * @author VeriVote
 */
public class TestDataGenerator {
    /**
     * The compositional framework.
     */
    private final FrameworkRepresentation framework;
    /**
     * All unary properties of this.framework.
     */
    private final List<Property> eligibleProperties;

    /**
     * Simple constructor.
     *
     * @param frameworkValue the framework
     */
    public TestDataGenerator(final FrameworkRepresentation frameworkValue) {
        this.framework = frameworkValue;
        this.eligibleProperties = new LinkedList<Property>();

        for (final Property property : this.framework.getProperties()) {
            if (property.getArity() == 1) {
                /*
                 * List<ComponentType> parameters = property.getParameters(); ComponentType
                 * parameter = parameters.get(0);
                 * if(parameter.getName().equals(this.framework.getAlias()) ||
                 * parameter.getName().equals(ExtendedPrologStrings.COMPOSABLE_MODULE)) {
                 * if(property.getName().equals("electoral_module")) continue;
                 *
                 * this.eligibleProperties.add(property); }
                 */
                this.eligibleProperties.add(property);
            }
        }
    }

    /**
     * Returns the power set of unary properties within a compositional framework.
     *
     * @return all possible combinations of properties
     */
    public List<List<Property>> getAllPossiblePropertySets() {
        final List<List<Property>> res = new ArrayList<List<Property>>();

        for (int i = 0; i < Math.pow(2, this.eligibleProperties.size()); i++) {
            res.add(new LinkedList<Property>());
        }

        for (int i = 0; i < this.eligibleProperties.size(); i++) {
            final Property p = this.eligibleProperties.get(i);

            for (int j = 0; j < Math.pow(2, this.eligibleProperties.size()); j++) {
                if (((j >> i) & 1) == 1) {
                    res.get(j).add(p);
                }
            }
        }

        return res;
    }

    /**
     * Returns random sets of unary properties.
     *
     * @param amount size of the set to be generated
     * @return the set of properties
     *  @throws IllegalArgumentException if too many properties are requested
     */
    public List<Property> getRandomComposableModuleProperties(final int amount)
            throws IllegalArgumentException {
        if (amount > this.eligibleProperties.size()) {
            throw new IllegalArgumentException();
        }

        final List<Property> res = new LinkedList<Property>();

        while (res.size() != amount) {
            final int idx = (int) (this.eligibleProperties.size() * Math.random());
            res.add(this.eligibleProperties.get(idx));
        }

        return res;
    }
}
