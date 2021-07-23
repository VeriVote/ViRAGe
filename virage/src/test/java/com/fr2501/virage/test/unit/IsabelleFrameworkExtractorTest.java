package com.fr2501.virage.test.unit;

import org.junit.Test;

import com.fr2501.virage.isabelle.IsabelleFrameworkExtractor;
import com.fr2501.virage.types.ExternalSoftwareUnavailableException;
import com.fr2501.virage.types.FrameworkRepresentation;
import com.fr2501.virage.types.IsabelleBuildFailedException;

/**
 * Test suite for {@link IsabelleFrameworkExtractor}.
 *
 * @author VeriVote
 */
public class IsabelleFrameworkExtractorTest {
    /**
     * Simple test.
     * @throws ExternalSoftwareUnavailableException if Isabelle is unavailable
     * @throws IsabelleBuildFailedException if the build process fails
     */
    @Test
    public void simpleTest()
            throws ExternalSoftwareUnavailableException, IsabelleBuildFailedException {
        final IsabelleFrameworkExtractor extractor = new IsabelleFrameworkExtractor();

        final FrameworkRepresentation framework = extractor.extract(
                "src/test/resources/verifiedVotingRuleConstruction/theories",
                "Verified_Voting_Rule_Construction");

        System.out.println(framework.toString());
    }
}
