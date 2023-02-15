package com.fr2501.virage.test.unit;

import org.junit.Test;

import com.fr2501.virage.isabelle.IsabelleFrameworkExtractor;
import com.fr2501.virage.types.FrameworkExtractionFailedException;
import com.fr2501.virage.types.FrameworkRepresentation;

/**
 * Test suite for {@link IsabelleFrameworkExtractor}.
 *
 * @author VeriVote
 */
public class IsabelleFrameworkExtractorTest {
    /**
     * Simple test.
     * @throws FrameworkExtractionFailedException wrapping the actual cause
     */
    @Test
    public void simpleTest() throws FrameworkExtractionFailedException {
        final IsabelleFrameworkExtractor extractor = new IsabelleFrameworkExtractor();

        final FrameworkRepresentation framework = extractor.extract(
                "src/test/resources/verifiedVotingRuleConstruction/theories",
                "Verified_Voting_Rule_Construction");

        System.out.println(framework.toString());
    }
}
