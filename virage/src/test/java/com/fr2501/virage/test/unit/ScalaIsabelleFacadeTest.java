package com.fr2501.virage.test.unit;

import org.junit.Test;

import com.fr2501.virage.isabelle.ScalaIsabelleFacade;
import com.fr2501.virage.types.ExternalSoftwareUnavailableException;
import com.fr2501.virage.types.IsabelleBuildFailedException;

/**
 * Test suite for {@link ScalaIsabelleFacade}.
 *
 * @author VeriVote
 */
public class ScalaIsabelleFacadeTest {
    /**
     * This test tries to create a ScalaIsabelleFacade object.
     * @throws ExternalSoftwareUnavailableException if Isabelle is unavailable
     * @throws IsabelleBuildFailedException if the Isabelle build process fails
     */
    @Test
    public void simpleTest()
            throws ExternalSoftwareUnavailableException, IsabelleBuildFailedException {
        @SuppressWarnings("unused")
        final ScalaIsabelleFacade facade = new ScalaIsabelleFacade(
                "src/test/resources/verifiedVotingRuleConstruction/theories",
                "Verified_Voting_Rule_Construction");
    }
}
