package edu.kit.kastel.formal.virage.test.unit;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.util.Map;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import org.junit.Test;

import edu.kit.kastel.formal.virage.prolog.JplFacade;
import edu.kit.kastel.formal.virage.prolog.QueryState;
import edu.kit.kastel.formal.virage.types.ExternalSoftwareUnavailableException;
import edu.kit.kastel.formal.virage.types.SearchResult;

/**
 * Test suite for {@link JplFacade}.
 *
 * @author VeriVote
 */
public class JplFacadeTest {
    /**
     * Test Prolog predicate name "".
     */
    private static final String EMPTY = "";

    /**
     * Test Prolog predicate name ",".
     */
    private static final String COMMA = ",";

    /**
     * Test Prolog predicate name "a".
     */
    private static final String A = "a";

    /**
     * Test Prolog predicate name "c".
     */
    private static final String C = "c";

    /**
     * Test Prolog predicate name "d".
     */
    private static final String D = "d";

    /**
     * Test Prolog predicate name "f".
     */
    private static final String F = "f";

    /**
     * Test Prolog predicate name "g".
     */
    private static final String G = "g";

    /**
     * Test Prolog predicate name "X".
     */
    private static final String X = "X";

    /**
     * Test Prolog predicate name "Y".
     */
    private static final String Y = "Y";

    /**
     * Test Prolog property name "property_a".
     */
    private static final String PROP_A = "property_a";

    /**
     * The logger.
     */
    private static final Logger LOGGER = LogManager.getLogger(JplFacadeTest.class);

    /**
     * Path to valid test file.
     */
    private static final String VALID_TEST_PATH = "src/test/resources/valid_test.pl";

    /**
     * Translates a predicate name and arguments to a test Prolog predicate.
     *
     * @param name the predicate name of the composed predicate
     * @param args the predicate's arguments
     * @return a test String representing the composed Prolog predicate
     */
    private static String predicate(final String name, final String... args) {
        String arg = EMPTY;
        for (final String a : args) {
            if (!arg.isEmpty()) {
                arg += COMMA;
            }
            arg += a;
        }
        return "name" + "(" + arg + ")";
    }

    /**
     * Tests an invalid query.
     * @throws ExternalSoftwareUnavailableException if JPL is unavailable
     */
    @Test
    public void testInvalidQuery() throws ExternalSoftwareUnavailableException {
        LOGGER.info("testInvalidQuery()");
        final JplFacade facade = new JplFacade(1000);

        final String query = "(,this is not a ) legit ,;. query @ all.)(";

        final SearchResult<Map<String, String>> result = facade.iterativeDeepeningQuery(query);

        assertTrue(result.getState() == QueryState.ERROR);
    }

    /**
     * Tests simple query.
     * @throws ExternalSoftwareUnavailableException if JPL is unavailable
     * @throws UnsatisfiedLinkError if JPL cannot be loaded correctly
     */
    @Test
    public void testSimpleQuery() throws UnsatisfiedLinkError,
            ExternalSoftwareUnavailableException {
        LOGGER.info("testSimpleQuery()");
        final JplFacade facade = new JplFacade(1000);
        facade.consultFile(VALID_TEST_PATH);

        final String query = predicate(PROP_A, X);

        final SearchResult<Map<String, String>> result = facade.iterativeDeepeningQuery(query);

        assertTrue(result.getState() == QueryState.SUCCESS);
    }

    /**
     * Tests fact query.
     * @throws UnsatisfiedLinkError if JPL cannot be loaded
     * @throws ExternalSoftwareUnavailableException if JPL is unavailable
     */
    @Test
    public void testFactQuery() throws UnsatisfiedLinkError, ExternalSoftwareUnavailableException {
        LOGGER.info("testFactQuery()");
        final JplFacade facade = new JplFacade(1000);
        facade.consultFile(VALID_TEST_PATH);

        String query = predicate(PROP_A, D);
        SearchResult<Boolean> result = facade.factQuery(query);
        boolean booleanResult = result.getValue();
        assertFalse(booleanResult);

        query = predicate(PROP_A, A);
        result = facade.factQuery(query);
        booleanResult = result.getValue();
        assertTrue(booleanResult);
    }

    /**
     * Tests simple unification query.
     * @throws ExternalSoftwareUnavailableException if JPL is unavailable
     */
    @Test
    public void testUnification() throws ExternalSoftwareUnavailableException {
        final JplFacade facade = new JplFacade(1000);

        final String generic = predicate(F, X);
        final String specific = predicate(F, A);

        Map<String, String> map = facade.unifiable(generic, specific);

        assertTrue(map.keySet().size() == 1);
        assertTrue(map.get(X).equals(A));

        final String first = predicate(G, X, predicate(F, C));
        final String second = predicate(G, D, Y);

        map = facade.unifiable(first, second);

        assertTrue(map.keySet().size() == 2);
        assertTrue(map.get(X).equals(D));
        assertTrue(map.get(Y).equals(predicate(F, C)));
    }
}
