package edu.kit.kastel.formal.virage.jobs;

import java.util.LinkedList;
import java.util.List;

import edu.kit.kastel.formal.util.StringUtils;
import edu.kit.kastel.formal.virage.core.ConfigReader;
import edu.kit.kastel.formal.virage.core.VirageUserInterface;
import edu.kit.kastel.formal.virage.types.CompositionProof;
import edu.kit.kastel.formal.virage.types.DecompositionTree;
import edu.kit.kastel.formal.virage.types.FrameworkRepresentation;
import edu.kit.kastel.formal.virage.types.Property;

/**
 * A {@link VirageJob} used to prove claims about properties of compositions.
 *
 * @author VeriVote
 */
public final class VirageProveJob
        extends VirageJobWithExplicitResult<List<List<CompositionProof>>> {
    /**
     * List of String representations of desired properties.
     */
    private final List<String> propertyStrings;

    /**
     * List of desired properties.
     */
    private List<Property> properties;

    /**
     * Composition to be checked.
     */
    private final DecompositionTree tree;

    /**
     * The framework representation.
     */
    private FrameworkRepresentation framework;

    /**
     * Simple constructor.
     *
     * @param issuer the issuing user interface
     * @param treeValue the tree
     * @param propertiesValue the properties
     */
    public VirageProveJob(final VirageUserInterface issuer, final String treeValue,
                          final List<String> propertiesValue) {
        super(issuer);
        this.tree = DecompositionTree.parseString(treeValue);
        this.propertyStrings = propertiesValue;
    }

    @Override
    public void concreteExecute() {
        this.framework = this.getExecutingCore().getFrameworkRepresentation();
        this.properties = new LinkedList<Property>();
        for (final String s: this.propertyStrings) {
            this.properties.add(this.framework.getProperty(s));
        }
        this.setResult(this.getExecutingCore().getSearchManager().proveClaims(this.tree,
                                                                              this.properties));
    }

    @Override
    public boolean externalSoftwareAvailable() {
        return ConfigReader.getInstance().hasJpl();
    }

    @Override
    public String getDescription() {
        return "Searching proof ...";
    }

    @Override
    public String presentConcreteResult() {
        return StringUtils.printCollection2(
                StringUtils.appendPeriod("Proof found"), this.tree.toString(),
                "satisfies the", this.properties.size() == 1 ? "property" : "properties",
                StringUtils.appendPeriod(StringUtils.printCollection(this.properties)));
    }
}
