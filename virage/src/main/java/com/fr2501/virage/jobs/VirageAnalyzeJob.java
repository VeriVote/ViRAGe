package com.fr2501.virage.jobs;

import com.fr2501.virage.core.ConfigReader;
import com.fr2501.virage.core.VirageSearchManager;
import com.fr2501.virage.core.VirageUserInterface;
import com.fr2501.virage.types.BooleanWithUncertainty;
import com.fr2501.virage.types.DecompositionTree;
import com.fr2501.virage.types.FrameworkRepresentation;
import com.fr2501.virage.types.Property;
import com.fr2501.virage.types.SearchResult;
import java.util.LinkedList;
import java.util.List;

/**
 * A {@link VirageJob} used to analyze a composition.
 *
 */
public class VirageAnalyzeJob
    extends VirageJobWithExplicitResult<List<List<SearchResult<BooleanWithUncertainty>>>> {
  private List<String> propertyStrings;
  private List<Property> properties;
  private DecompositionTree tree;

  private FrameworkRepresentation framework;
  private VirageSearchManager manager;

  /**
   * Simple constructor.

   * @param issuer the issuer
   * @param tree the tree
   * @param properties the properties
   */
  public VirageAnalyzeJob(VirageUserInterface issuer, String tree, List<String> properties) {
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

    this.result = this.manager.analyzeComposition(tree, properties);
  }

  @Override
  public List<List<SearchResult<BooleanWithUncertainty>>> getResult() {
    return this.result;
  }

  @Override
  public boolean externalSoftwareAvailable() {
    return (ConfigReader.getInstance().hasJpl());
  }
}
