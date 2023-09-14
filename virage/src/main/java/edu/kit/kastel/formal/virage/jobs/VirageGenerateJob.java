package edu.kit.kastel.formal.virage.jobs;

import java.util.LinkedList;
import java.util.List;

import edu.kit.kastel.formal.util.StringUtils;
import edu.kit.kastel.formal.virage.core.ConfigReader;
import edu.kit.kastel.formal.virage.core.VirageCore;
import edu.kit.kastel.formal.virage.core.VirageSearchManager;
import edu.kit.kastel.formal.virage.core.VirageUserInterface;
import edu.kit.kastel.formal.virage.types.DecompositionTree;
import edu.kit.kastel.formal.virage.types.Property;
import edu.kit.kastel.formal.virage.types.SearchResult;

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
     * @param issuer the issuing user interface
     * @param propertiesValue the properties
     */
    public VirageGenerateJob(final VirageUserInterface issuer, final List<String> propertiesValue) {
        super(issuer);
        this.propertyStrings = propertiesValue;
    }

    @Override
    public void concreteExecute() {
        final VirageCore execCore = this.getExecutingCore();
        this.manager = execCore.getSearchManager();
        this.properties = new LinkedList<Property>();
        for (final String s: this.propertyStrings) {
            this.properties.add(execCore.getFrameworkRepresentation().getProperty(s));
        }
        this.setResult(this.manager.generateComposition(this.properties));
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
        for (final SearchResult<DecompositionTree> treeResult: this.getResult()) {
            if (treeResult.hasValue()) {
                final DecompositionTree tree = treeResult.getValue();
                results.add(tree.toStringWithTypesInsteadOfVariables(
                        this.getExecutingCore().getFrameworkRepresentation()));
            }
        }
        if (results.isEmpty()) {
            return StringUtils.appendPeriod(
                    StringUtils.printCollection2(
                            "No composition found with", prop,
                            StringUtils.printCollection(this.properties)));
        }
        if (results.contains(StringUtils.EMPTY)) {
            return StringUtils.appendPeriod(
                    StringUtils.printCollection2(
                            "Any component of type",
                            this.properties.get(0).getParameters().get(0).getName(),
                            "satisfies the", prop, StringUtils.printCollection(this.properties)));
        }
        return StringUtils.appendPeriod(
                StringUtils.printCollection2(
                        "Generated the",
                        this.properties.get(0).getParameters().get(0).getName(),
                        "\"" + StringUtils.printCollection(results) + "\" with the",
                        prop, StringUtils.printCollection(this.properties)));
    }
}
