package com.fr2501.virage.test.unit;


import com.fr2501.virage.isabelle.IsabelleFrameworkExtractor;
import com.fr2501.virage.types.ExternalSoftwareUnavailableException;
import com.fr2501.virage.types.FrameworkRepresentation;
import com.fr2501.virage.types.IsabelleBuildFailedException;
import org.junit.Test;

public class IsabelleFrameworkExtractorTest {
  @Test
  public void simpleTest()
      throws ExternalSoftwareUnavailableException, IsabelleBuildFailedException {
    IsabelleFrameworkExtractor extractor = new IsabelleFrameworkExtractor();

    FrameworkRepresentation framework = extractor.extract(
        "src/test/resources/verifiedVotingRuleConstruction/theories",
        "Verified_Voting_Rule_Construction");

    System.out.println(framework.toString());
  }
}
