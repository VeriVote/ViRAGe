package edu.kit.kastel.formal.virage.test.unit;

import org.junit.Test;

import edu.kit.kastel.formal.util.SystemUtils;
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
     * The path of the theories directory.
     */
    private static final String DIRECTORY_PATH =
            SystemUtils.RESOURCES + "verifiedVotingRuleConstruction/theories";

    /**
     * The name of the Isabelle session.
     */
    private static final String SESSION_NAME = "Verified_Voting_Rule_Construction";

    /**
     * Simple test.
     *
     * @throws FrameworkExtractionFailedException wrapping the actual cause
     */
    @Test
    public void simpleTest() throws FrameworkExtractionFailedException {
        final IsabelleFrameworkExtractor extractor = new IsabelleFrameworkExtractor();
        final FrameworkRepresentation framework = extractor.extract(DIRECTORY_PATH, SESSION_NAME);
        System.out.println(framework.toString());
    }
}
