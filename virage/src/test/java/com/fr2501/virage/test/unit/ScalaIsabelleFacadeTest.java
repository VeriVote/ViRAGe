package com.fr2501.virage.test.unit;

import com.fr2501.virage.isabelle.ScalaIsabelleFacade;
import com.fr2501.virage.types.ExternalSoftwareUnavailableException;
import com.fr2501.virage.types.IsabelleBuildFailedException;

/**
 * Test suite for {@link ScalaIsabelleFacade}.
 *
 * @author VeriVote
 */
public class ScalaIsabelleFacadeTest {
    // Currently disabled. It is entirely covered by IsabelleFrameworkExtractorTest
    // and scala-isabelle causes problems on the second invocation in the same JVM.
    /**
     * This test tries to create a ScalaIsabelleFacade object.
     * @throws ExternalSoftwareUnavailableException if Isabelle is unavailable
     * @throws IsabelleBuildFailedException if the Isabelle build process fails
     */
    public void simpleTest()
            throws ExternalSoftwareUnavailableException, IsabelleBuildFailedException {
        @SuppressWarnings("unused")
        final ScalaIsabelleFacade facade = new ScalaIsabelleFacade(
                "src/test/resources/verifiedVotingRuleConstruction/theories",
                "Verified_Voting_Rule_Construction");
    }
}
