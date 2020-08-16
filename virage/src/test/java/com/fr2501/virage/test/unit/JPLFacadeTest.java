package com.fr2501.virage.test.unit;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.util.Map;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import org.junit.Test;

import com.fr2501.virage.prolog.JPLFacade;
import com.fr2501.virage.prolog.QueryState;
import com.fr2501.virage.types.SearchResult;

public class JPLFacadeTest {
	private static final Logger logger = LogManager.getLogger(JPLFacadeTest.class);
	private static final String validTestPath = "src/test/resources/valid_test.pl";
	
	@Test
	public void testInvalidQuery() {
		logger.info("testInvalidQuery()");
		JPLFacade facade = new JPLFacade(1000);
		
		String query = "(,this is not a ) legit ,;. query @ all.)(";
		
		SearchResult<Map<String,String>> result = facade.iterativeDeepeningQuery(query);
		
		assertTrue(result.getState() == QueryState.ERROR);
	}
	
	@Test
	public void testSimpleQuery() throws Exception {
		logger.info("testSimpleQuery()");
		JPLFacade facade = new JPLFacade(1000);
		facade.consultFile(validTestPath);
		
		String query = "property_a(X)";
		
		SearchResult<Map<String, String>> result = facade.iterativeDeepeningQuery(query);
		
		assertTrue(result.getState() == QueryState.SUCCESS);
	}
	
	@Test
	public void testFactQuery() throws Exception {
		logger.info("testFactQuery()");
		JPLFacade facade = new JPLFacade(1000);
		facade.consultFile(validTestPath);
		
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
	public void testUnification() {
		JPLFacade facade = new JPLFacade(1000);
		
		String generic = "f(X)";
		String specific = "f(a)";
		
		Map<String,String> map = facade.unifiable(generic, specific);
		
		assertTrue(map.keySet().size() == 1);
		assertTrue(map.get("X").equals("a"));
		
		String first = "g(X,f(c))";
		String second = "g(d,Y)";
		
		map = facade.unifiable(first, second);
		
		assertTrue(map.keySet().size() == 2);
		assertTrue(map.get("X").equals("d"));
		assertTrue(map.get("Y").equals("f(c)"));
	}
}
