package com.fr2501.virage;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.io.File;
import java.io.IOException;
import java.util.HashMap;
import java.util.Map;
import java.util.Set;

import org.jpl7.PrologException;
import org.junit.Before;
import org.junit.Test;

import com.fr2501.virage.prolog.ExtendedPrologParser;
import com.fr2501.virage.prolog.JPLFacade;
import com.fr2501.virage.prolog.MalformedEPLFileException;
import com.fr2501.virage.prolog.SimpleExtendedPrologParser;
import com.fr2501.virage.types.FrameworkRepresentation;
import com.fr2501.virage.types.Property;
import com.fr2501.virage.types.SearchResult;

public class JPLFacadeTest {
	private static final String validTestPath = "src/test/resources/valid_test.pl";
	
	@Test(expected = PrologException.class)
	public void testMalformedQuery() {
		JPLFacade facade = new JPLFacade(1000);
		
		String query = "(,this is not a ) legit ,;. query @ all.)(";
		
		facade.query(query);
	}
	
	@Test
	public void testSimpleQuery() throws Exception {
		JPLFacade facade = new JPLFacade(1000);
		facade.consultFile(validTestPath);
		
		String query = "property_a(X)";
		
		SearchResult<Set<Map<String, String>>> result = facade.query(query);
		
		Set<Map<String, String>> results = result.getValue();
		
		assertTrue(results.size() == 2);
		
		Map<String, String> a = new HashMap<String, String>();
		a.put("X", "a");
		Map<String, String> b = new HashMap<String, String>();
		b.put("X", "b");
		
		assertTrue(results.contains(a));
		assertTrue(results.contains(b));
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
