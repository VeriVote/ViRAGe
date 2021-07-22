package com.fr2501.virage.test.unit;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.util.Map;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import org.junit.Test;

import com.fr2501.virage.prolog.JplFacade;
import com.fr2501.virage.prolog.QueryState;
import com.fr2501.virage.types.ExternalSoftwareUnavailableException;
import com.fr2501.virage.types.SearchResult;

/**
 * Test suite for {@link JplFacade}.
 *
 */
public class JplFacadeTest {
    private static final Logger LOGGER = LogManager.getLogger(JplFacadeTest.class);
    private static final String VALID_TEST_PATH = "src/test/resources/valid_test.pl";

    @Test
    public void testInvalidQuery() throws ExternalSoftwareUnavailableException {
        LOGGER.info("testInvalidQuery()");
        final JplFacade facade = new JplFacade(1000);

        final String query = "(,this is not a ) legit ,;. query @ all.)(";

        final SearchResult<Map<String, String>> result = facade.iterativeDeepeningQuery(query);

        assertTrue(result.getState() == QueryState.ERROR);
    }

    @Test
    public void testSimpleQuery() throws Exception {
        LOGGER.info("testSimpleQuery()");
        final JplFacade facade = new JplFacade(1000);
        facade.consultFile(VALID_TEST_PATH);

        final String query = "property_a(X)";

        final SearchResult<Map<String, String>> result = facade.iterativeDeepeningQuery(query);

        assertTrue(result.getState() == QueryState.SUCCESS);
    }

    @Test
    public void testFactQuery() throws Exception {
        LOGGER.info("testFactQuery()");
        final JplFacade facade = new JplFacade(1000);
        facade.consultFile(VALID_TEST_PATH);

        String query = "property_a(d)";
        SearchResult<Boolean> result = facade.factQuery(query);
        boolean booleanResult = result.getValue();
        assertFalse(booleanResult);

        query = "property_a(a)";
        result = facade.factQuery(query);
        booleanResult = result.getValue();
        assertTrue(booleanResult);
    }

    @Test
    public void testUnification() throws ExternalSoftwareUnavailableException {
        final JplFacade facade = new JplFacade(1000);

        final String generic = "f(X)";
        final String specific = "f(a)";

        Map<String, String> map = facade.unifiable(generic, specific);

        assertTrue(map.keySet().size() == 1);
        assertTrue(map.get("X").equals("a"));

        final String first = "g(X,f(c))";
        final String second = "g(d,Y)";

        map = facade.unifiable(first, second);

        assertTrue(map.keySet().size() == 2);
        assertTrue(map.get("X").equals("d"));
        assertTrue(map.get("Y").equals("f(c)"));
    }
}
