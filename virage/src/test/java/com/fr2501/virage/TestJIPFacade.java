package com.fr2501.virage;

import java.io.File;
import java.io.IOException;

import org.junit.BeforeClass;
import org.junit.Test;

import com.fr2501.virage.prolog.ExtendedPrologParser;
import com.fr2501.virage.prolog.JIPQueryManager;
import com.fr2501.virage.prolog.JIPQueryManagerFactory;
import com.fr2501.virage.prolog.MalformedEPLFileException;
import com.fr2501.virage.prolog.SimpleExtendedPrologParser;
import com.fr2501.virage.types.FrameworkRepresentation;

public class TestJIPFacade {
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
		JIPQueryManager manager = JIPQueryManagerFactory.getJIPQueryManager(framework);
		
		manager.openBlockingQuery("?- electing(X).");
	}
	
	@Test
	public void testSMCMonotone() {
		String query = "monotone(sequential_composition(" + 
				                             "loop_composition(" + 
				                                 "parallel_composition(" + 
				                                     "sequential_composition(" + 
				                                         "pass_module(2)," + 
				                                         "sequential_composition(" + 
				                                             "downgrade(" + 
				                                                 "plurality_module)," + 
				                                             "pass_module(1)))," + 
				                                     "drop_module(2)," + 
				                                     "max_aggregator)," + 
				                                 "defer_eq_condition(1))," + 
				                             "elect_module)).";
		
		JIPQueryManager manager = JIPQueryManagerFactory.getJIPQueryManager(framework);
		
		manager.openBlockingQuery(query);
	}
}
