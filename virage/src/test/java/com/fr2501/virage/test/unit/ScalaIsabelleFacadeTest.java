package com.fr2501.virage.test.unit;

import com.fr2501.virage.isabelle.ScalaIsabelleFacade;
import com.fr2501.virage.types.ExternalSoftwareUnavailableException;
import com.fr2501.virage.types.IsabelleBuildFailedException;
import org.junit.Test;

public class ScalaIsabelleFacadeTest {
  @Test
  public void simpleTest()
      throws ExternalSoftwareUnavailableException, IsabelleBuildFailedException {
    @SuppressWarnings("unused")
    ScalaIsabelleFacade facade = new ScalaIsabelleFacade(
        "src/test/resources/verifiedVotingRuleConstruction/theories",
        "Verified_Voting_Rule_Construction");
  }
}
