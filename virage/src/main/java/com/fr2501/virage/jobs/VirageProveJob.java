package com.fr2501.virage.jobs;

import com.fr2501.virage.core.ConfigReader;
import com.fr2501.virage.core.VirageSearchManager;
import com.fr2501.virage.core.VirageUserInterface;
import com.fr2501.virage.types.CompositionProof;
import com.fr2501.virage.types.DecompositionTree;
import com.fr2501.virage.types.FrameworkRepresentation;
import com.fr2501.virage.types.Property;
import java.util.LinkedList;
import java.util.List;

/**
 * A {@link VirageJob} used to prove claims about properties of compositions.
 *
 */
public class VirageProveJob extends VirageJobWithExplicitResult<List<List<CompositionProof>>> {
  private List<String> propertyStrings;
  private List<Property> properties;
  private DecompositionTree tree;

  private FrameworkRepresentation framework;
  private VirageSearchManager manager;

  /**
   * Simple constructor.

   * @param issuer the issuing ui
   * @param tree the tree
   * @param properties the properties
   */
  public VirageProveJob(VirageUserInterface issuer, String tree, List<String> properties) {
    super(issuer);

    this.tree = DecompositionTree.parseString(tree);
    this.propertyStrings = properties;
  }

  @Override
  public void concreteExecute() {
    this.framework = this.executingCore.getFrameworkRepresentation();
    this.manager = this.executingCore.getSearchManager();

    this.properties = new LinkedList<Property>();

    for (String s : this.propertyStrings) {
      this.properties.add(this.framework.getProperty(s));
    }

    this.result = this.manager.proveClaims(tree, properties);
  }

  @Override
  public List<List<CompositionProof>> getResult() {
    return this.result;
  }

  @Override
  public boolean externalSoftwareAvailable() {
    return (ConfigReader.getInstance().hasJpl());
  }
}
