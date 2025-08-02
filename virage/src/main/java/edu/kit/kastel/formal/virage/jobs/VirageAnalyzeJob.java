package edu.kit.kastel.formal.virage.jobs;

import java.util.LinkedList;
import java.util.List;

import edu.kit.kastel.formal.util.StringUtils;
import edu.kit.kastel.formal.virage.core.ConfigReader;
import edu.kit.kastel.formal.virage.core.VirageSearchManager;
import edu.kit.kastel.formal.virage.core.VirageUserInterface;
import edu.kit.kastel.formal.virage.types.BooleanWithUncertainty;
import edu.kit.kastel.formal.virage.types.DecompositionTree;
import edu.kit.kastel.formal.virage.types.FrameworkRepresentation;
import edu.kit.kastel.formal.virage.types.Property;
import edu.kit.kastel.formal.virage.types.SearchResult;

/**
 * A {@link VirageJob} used to analyze a composition.
 *
 * @author VeriVote
 */
public final class VirageAnalyzeJob
    extends VirageJobWithExplicitResult<List<List<SearchResult<BooleanWithUncertainty>>>> {
    /**
     * String representation of the desired properties.
     */
    private final List<String> propertyStrings;

    /**
     * The desired properties.
     */
    private List<Property> properties;

    /**
     * The composition.
     */
    private final DecompositionTree tree;

    /**
     * Simple constructor.
     *
     * @param issuer the issuer
     * @param treeValue the tree
     * @param propertiesValue the properties
     */
    public VirageAnalyzeJob(final VirageUserInterface issuer, final String treeValue,
            final List<String> propertiesValue) {
        super(issuer);
        this.tree = DecompositionTree.parseString(treeValue);
        this.propertyStrings = propertiesValue;
    }

    @Override
    public void concreteExecute() {
        final FrameworkRepresentation framework =
                this.getExecutingCore().getFrameworkRepresentation();
        final VirageSearchManager manager = this.getExecutingCore().getSearchManager();
        this.properties = new LinkedList<Property>();
        for (final String s: this.propertyStrings) {
            this.properties.add(framework.getProperty(s));
        }
        this.setResult(manager.analyzeComposition(this.tree, this.properties));
    }

    @Override
    public boolean externalSoftwareAvailable() {
        return ConfigReader.getInstance().hasJpl();
    }

    @Override
    public String getDescription() {
        return "Analyzing a composition ...";
    }

    @Override
    public String presentConcreteResult() {
        String prop = "properties";
        if (this.properties.size() == 1) {
            prop = "property";
        }
        boolean hasProperties = false;
        for (final List<SearchResult<BooleanWithUncertainty>> resultList: this.getResult()) {
            for (final SearchResult<BooleanWithUncertainty> result: resultList) {
                if (result.hasValue() && result.getValue() == BooleanWithUncertainty.TRUE) {
                    hasProperties = true;
                    break;
                }
            }
        }
        final String hasOrNot = hasProperties ? "has" : "cannot be shown to have";
        return StringUtils.printCollection2(
                this.tree.toString(), hasOrNot, "the", prop,
                StringUtils.printCollection(this.properties));
    }
}
