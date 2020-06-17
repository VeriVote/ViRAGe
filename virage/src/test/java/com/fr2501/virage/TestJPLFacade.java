package com.fr2501.virage;

import java.io.File;
import java.io.IOException;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.jpl7.Atom;
import org.jpl7.Compound;
import org.jpl7.Query;
import org.jpl7.Term;
import org.jpl7.Variable;
import org.junit.BeforeClass;
import org.junit.Test;

import com.fr2501.virage.prolog.ExtendedPrologParser;
import com.fr2501.virage.prolog.JPLFacade;
import com.fr2501.virage.prolog.MalformedEPLFileException;
import com.fr2501.virage.prolog.QueryResult;
import com.fr2501.virage.prolog.SimpleExtendedPrologParser;
import com.fr2501.virage.types.FrameworkRepresentation;

public class TestJPLFacade {
	private static ExtendedPrologParser parser;
	private static FrameworkRepresentation framework;
	private static final String path = "src/main/resources/framework.pl";
	
	@BeforeClass
	public static void setup() {
		parser = new SimpleExtendedPrologParser();
		try {
			framework = parser.parseFramework(new File(path));
		} catch (IOException e) {
			e.printStackTrace();
		} catch (MalformedEPLFileException e) {
			e.printStackTrace();
		}
	}
	
	@Test
	public void testNothing() throws InterruptedException {
		JPLFacade facade = new JPLFacade(framework, 100);
		
		facade.consultFile("src/main/resources/framework.pl");
		
		Set<Map<String, String>> res = facade.iterativeDeepeningQuery("electing(X)", 5);
		
		for(Map<String, String> map: res) {
			System.out.println("---");
			
			for(String key: map.keySet()) {
				System.out.println(key + ": " + map.get(key));
			}
		}
	}
}
