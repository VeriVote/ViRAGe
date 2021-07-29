package com.fr2501.virage.jobs;

import java.util.LinkedList;
import java.util.List;

import com.fr2501.util.StringUtils;
import com.fr2501.virage.core.ConfigReader;
import com.fr2501.virage.core.VirageSearchManager;
import com.fr2501.virage.core.VirageUserInterface;
import com.fr2501.virage.types.DecompositionTree;
import com.fr2501.virage.types.Property;
import com.fr2501.virage.types.SearchResult;

/**
 * A {@link VirageJob} used for generating compositions.
 *
 * @author VeriVote
 */
public final class VirageGenerateJob
        extends VirageJobWithExplicitResult<List<SearchResult<DecompositionTree>>> {
    /**
     * String representations of the desired properties.
     */
    private final List<String> propertyStrings;
    /**
     * The desired properties.
     */
    private List<Property> properties;

    /**
     * The search manager to be used.
     */
    private VirageSearchManager manager;

    /**
     * Simple constructor.
     *
     * @param issuer the issuing ui
     * @param propertiesValue the properties
     */
    public VirageGenerateJob(final VirageUserInterface issuer, final List<String> propertiesValue) {
        super(issuer);

        this.propertyStrings = propertiesValue;
    }

    @Override
    public void concreteExecute() {
        this.manager = this.getExecutingCore().getSearchManager();

        this.properties = new LinkedList<Property>();

        for (final String s : this.propertyStrings) {
            this.properties
                    .add(this.getExecutingCore().getFrameworkRepresentation().getProperty(s));
        }

        this.result = this.manager.generateComposition(this.properties);
    }

    @Override
    public boolean externalSoftwareAvailable() {
        return ConfigReader.getInstance().hasJpl();
    }

    @Override
    public String getDescription() {
        return "Generating Composition ...";
    }

    @Override
    public String presentConcreteResult() {
        String prop = "properties";
        if (this.properties.size() == 1) {
            prop = "property";
        }

        final List<String> results = new LinkedList<String>();
        for (final SearchResult<DecompositionTree> treeResult : this.result) {
            if (treeResult.hasValue()) {
                final DecompositionTree tree = treeResult.getValue();

                results.add(tree.toStringWithTypesInsteadOfVariables(
                        this.getExecutingCore().getFrameworkRepresentation()));
            }
        }

        if (results.isEmpty()) {
            return "No composition found with " + prop + " "
                    + StringUtils.printCollection(this.properties) + ".";
        }

        if (results.contains("")) {
            return "Any component of type "
                    + this.properties.get(0).getParameters().get(0).getName() + " satisfies the "
                    + prop + " " + StringUtils.printCollection(this.properties) + ".";
        }

        return "Generated the " + this.properties.get(0).getParameters().get(0).getName() + " \""
                + StringUtils.printCollection(results) + "\" with the " + prop + " "
                + StringUtils.printCollection(this.properties) + ".";
    }
}
