package com.fr2501.virage.jobs;

import java.util.LinkedList;
import java.util.List;

import com.fr2501.util.StringUtils;
import com.fr2501.virage.core.ConfigReader;
import com.fr2501.virage.core.VirageUserInterface;
import com.fr2501.virage.types.CompositionProof;
import com.fr2501.virage.types.DecompositionTree;
import com.fr2501.virage.types.FrameworkRepresentation;
import com.fr2501.virage.types.Property;

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
     * @param issuer the issuing ui
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

        for (final String s : this.propertyStrings) {
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
        String prop = "properties";
        if (this.properties.size() == 1) {
            prop = "property";
        }

        final String res = "Proof found. " + this.tree.toString() + " satisfies the " + prop + " "
                + StringUtils.printCollection(this.properties) + ".";

        return res;
    }
}
