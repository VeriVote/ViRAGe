package com.fr2501.virage.jobs;

import com.fr2501.util.StringUtils;
import com.fr2501.virage.core.ConfigReader;
import com.fr2501.virage.core.VirageSearchManager;
import com.fr2501.virage.core.VirageUserInterface;
import com.fr2501.virage.types.DecompositionTree;
import com.fr2501.virage.types.FrameworkRepresentation;
import com.fr2501.virage.types.Property;
import com.fr2501.virage.types.SearchResult;
import java.util.LinkedList;
import java.util.List;

/**
 * A {@link VirageJob} used for generating compositions.
 *
 */
public class VirageGenerateJob
    extends VirageJobWithExplicitResult<List<SearchResult<DecompositionTree>>> {
  private List<String> propertyStrings;
  private List<Property> properties;

  private FrameworkRepresentation framework;
  private VirageSearchManager manager;

  /**
   * Simple constructor.

   * @param issuer the issuing ui
   * @param properties the properties
   */
  public VirageGenerateJob(VirageUserInterface issuer, List<String> properties) {
    super(issuer);

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

    this.result = this.manager.generateComposition(properties);
  }

  @Override
  public List<SearchResult<DecompositionTree>> getResult() {
    return this.result;
  }

  @Override
  public boolean externalSoftwareAvailable() {
    return (ConfigReader.getInstance().hasJpl());
  }

  @Override
  public String presentConcreteResult() {
    String prop = "properties";
    if (this.properties.size() == 1) {
      prop = "property";
    }

    List<String> results = new LinkedList<String>();
    for (SearchResult<DecompositionTree> tree : this.result) {
      if (tree.hasValue()) {
        results.add(tree.getValue().toString());
      }
    }

    if (results.isEmpty()) {
      return "No composition found with " + prop + " "
          + StringUtils.printCollection(this.properties) + ".";
    }
    
    return "Generated " + StringUtils.printCollection(results) + " with " + prop + " "
        + StringUtils.printCollection(this.properties) + ".";
  }

  @Override
  public String getDescription() {
    return "Generating Composition ...";
  }
}
