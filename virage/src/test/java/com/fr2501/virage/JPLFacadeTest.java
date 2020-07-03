package com.fr2501.virage;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.util.Map;

import org.junit.Test;

import com.fr2501.virage.prolog.JPLFacade;
import com.fr2501.virage.prolog.QueryState;
import com.fr2501.virage.types.SearchResult;

public class JPLFacadeTest {
	private static final String validTestPath = "src/test/resources/valid_test.pl";
	
	@Test
	public void testInvalidQuery() {
		JPLFacade facade = new JPLFacade(1000);
		
		String query = "(,this is not a ) legit ,;. query @ all.)(";
		
		SearchResult<Map<String,String>> result = facade.iterativeDeepeningQuery(query);
		
		assertTrue(result.getState() == QueryState.ERROR);
	}
	
	@Test
	public void testSimpleQuery() throws Exception {
		JPLFacade facade = new JPLFacade(1000);
		facade.consultFile(validTestPath);
		
		String query = "property_a(X)";
		
		SearchResult<Map<String, String>> result = facade.iterativeDeepeningQuery(query);
		
		assertTrue(result.getState() == QueryState.SUCCESS);
	}
	
	@Test
	public void testFactQuery() throws Exception {
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
}
