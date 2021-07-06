package com.fr2501.virage.test.unit;

import com.fr2501.virage.types.FrameworkRepresentation;
import com.fr2501.virage.types.Property;
import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;

/**
 * Creates different kinds of test data.
 *
 */
public class TestDataGenerator {
    private FrameworkRepresentation framework;
    private List<Property> eligibleProperties;

    /**
     * Simple constructor.
     * 
     * @param framework the framework
     */
    public TestDataGenerator(FrameworkRepresentation framework) {
        this.framework = framework;
        this.eligibleProperties = new LinkedList<Property>();

        for (Property property : this.framework.getProperties()) {
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
     * Returns random sets of unary properties.
     * 
     * @param amount size of the set to be generated
     * @return the set of properties
     */
    public List<Property> getRandomComposableModuleProperties(int amount) {
        if (amount > eligibleProperties.size()) {
            throw new IllegalArgumentException();
        }

        List<Property> res = new LinkedList<Property>();

        while (res.size() != amount) {
            int idx = (int) (eligibleProperties.size() * Math.random());
            res.add(eligibleProperties.get(idx));
        }

        return res;
    }

    /**
     * Returns the power set of unary properties within a compositional framework.
     * 
     * @return all possible combinations of properties
     */
    public List<List<Property>> getAllPossiblePropertySets() {
        List<List<Property>> res = new ArrayList<List<Property>>();

        for (int i = 0; i < Math.pow(2, this.eligibleProperties.size()); i++) {
            res.add(new LinkedList<Property>());
        }

        for (int i = 0; i < this.eligibleProperties.size(); i++) {
            Property p = this.eligibleProperties.get(i);

            for (int j = 0; j < Math.pow(2, this.eligibleProperties.size()); j++) {
                if (((j >> i) & 1) == 1) {
                    res.get(j).add(p);
                }
            }
        }

        return res;
    }
}
