package com.fr2501.virage.test.eval;

import com.fr2501.util.StringUtils;
import com.fr2501.virage.analyzer.CompositionAnalyzer;
import com.fr2501.virage.prolog.JplFacade;
import com.fr2501.virage.prolog.QueryState;
import com.fr2501.virage.types.BooleanWithUncertainty;
import com.fr2501.virage.types.CompositionProof;
import com.fr2501.virage.types.DecompositionTree;
import com.fr2501.virage.types.ExternalSoftwareUnavailableException;
import com.fr2501.virage.types.FrameworkRepresentation;
import com.fr2501.virage.types.Property;
import com.fr2501.virage.types.SearchResult;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

public class StandardPrologCompositionAnalyzer implements CompositionAnalyzer {
  protected static final long DEFAULT_TIMEOUT = 10000;
  protected JplFacade facade;
  protected FrameworkRepresentation framework;

  private long timeout;

  public StandardPrologCompositionAnalyzer(FrameworkRepresentation framework)
      throws ExternalSoftwareUnavailableException {
    this.framework = framework;

    this.facade = new JplFacade(DEFAULT_TIMEOUT);
    this.timeout = DEFAULT_TIMEOUT;
    this.consultKnowledgeBase();
  }

  protected void consultKnowledgeBase() {
    this.facade.consultFile(this.framework.getAbsolutePath());
    this.facade.consultFile(this.getClass().getClassLoader().getResource("meta_interpreter.pl"));
  }

  @Override
  public SearchResult<DecompositionTree> generateComposition(List<Property> properties) {
    for (Property property : properties) {
      if (property.getArity() != 1) {
        throw new IllegalArgumentException();
      }
    }

    // Safety measure to ensure all properties talking about the same element.
    List<String> propertyStrings = new LinkedList<String>();
    for (Property property : properties) {
      propertyStrings.add(property.getInstantiatedString("X"));
    }

    String query = StringUtils.printCollection(propertyStrings);

    try {
      Map<String, String> result = this.facade.simpleQueryWithTimeout(query, this.timeout);

      if (result.isEmpty()) {
        return new SearchResult<DecompositionTree>(QueryState.TIMEOUT, null);
      }

      return new SearchResult<DecompositionTree>(QueryState.SUCCESS, null);

    } catch (Exception e) {
      return new SearchResult<DecompositionTree>(QueryState.FAILED, null);
    }

  }

  @Override
  public void setTimeout(long millis) {
    this.timeout = millis;
    this.facade.setTimeout(millis);
  }

  @Override
  public List<SearchResult<BooleanWithUncertainty>> analyzeComposition(
      DecompositionTree composition, List<Property> properties) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public List<CompositionProof> proveClaims(DecompositionTree composition,
      List<Property> properties) throws IllegalArgumentException {
    // TODO Auto-generated method stub
    return null;
  }
}
