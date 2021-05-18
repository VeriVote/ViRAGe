package com.fr2501.virage.test.unit;

import java.io.IOException;

import org.junit.Test;

import com.fr2501.virage.analyzer.SimplePrologCompositionAnalyzer;
import com.fr2501.virage.isabelle.IsabelleFrameworkExtractor;
import com.fr2501.virage.isabelle.ScalaIsabelleFacade;
import com.fr2501.virage.types.ExternalSoftwareUnavailableException;
import com.fr2501.virage.types.FrameworkRepresentation;

public class IsabelleFrameworkExtractorTest {
  @Test
  public void simpleTest() throws IOException, ExternalSoftwareUnavailableException {
    IsabelleFrameworkExtractor extractor = new IsabelleFrameworkExtractor();

    FrameworkRepresentation framework = extractor.extract("src/test/resources/verifiedVotingRuleConstruction/theories",
        "Verified_Voting_Rule_Construction");

    System.out.println(framework.toString());

    SimplePrologCompositionAnalyzer analyzer = new SimplePrologCompositionAnalyzer(framework);
    // analyzer.analyzeComposition("defer_module");
  }
}
