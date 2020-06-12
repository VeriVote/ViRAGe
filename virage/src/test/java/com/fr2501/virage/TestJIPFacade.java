package com.fr2501.virage;

import java.io.File;
import java.io.IOException;

import org.junit.BeforeClass;
import org.junit.Test;

import com.fr2501.virage.prolog.ExtendedPrologParser;
import com.fr2501.virage.prolog.JIPFacade;
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

	}
}
