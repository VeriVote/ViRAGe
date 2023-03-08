package edu.kit.kastel.formal.virage.test.unit;

import org.junit.Test;

import edu.kit.kastel.formal.virage.isabelle.IsabelleFrameworkExtractor;
import edu.kit.kastel.formal.virage.types.FrameworkExtractionFailedException;
import edu.kit.kastel.formal.virage.types.FrameworkRepresentation;

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
