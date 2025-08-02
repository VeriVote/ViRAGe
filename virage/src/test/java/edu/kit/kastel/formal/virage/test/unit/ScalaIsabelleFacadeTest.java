package edu.kit.kastel.formal.virage.test.unit;

import org.junit.jupiter.api.Assertions;

import edu.kit.kastel.formal.util.SystemUtils;
import edu.kit.kastel.formal.virage.isabelle.ScalaIsabelleFacade;
import edu.kit.kastel.formal.virage.types.ExternalSoftwareUnavailableException;
import edu.kit.kastel.formal.virage.types.IsabelleBuildFailedException;

/**
 * Test suite for {@link ScalaIsabelleFacade}.
 *
 * @author VeriVote
 */
public class ScalaIsabelleFacadeTest {
    /**
     * The test session directory.
     */
    private static final String SESSION_DIR_VALUE =
            SystemUtils.RESOURCES + "verifiedVotingRuleConstruction/theories";

    /**
     * The test session name.
     */
    private static final String SESSION_NAME_VALUE = "Verified_Voting_Rule_Construction";

    /**
     * This test tries to create a ScalaIsabelleFacade object.
     *
     * <b>Notice: </b> Currently disabled. It is entirely covered by IsabelleFrameworkExtractorTest
     * and scala-isabelle causes problems on the second invocation in the same JVM.
     *
     * @throws ExternalSoftwareUnavailableException if Isabelle is unavailable
     * @throws IsabelleBuildFailedException if the Isabelle build process fails
     */
    public void simpleTest()
            throws ExternalSoftwareUnavailableException, IsabelleBuildFailedException {
        Assertions.assertDoesNotThrow(()
                -> new ScalaIsabelleFacade(SESSION_DIR_VALUE, SESSION_NAME_VALUE));
    }
}
