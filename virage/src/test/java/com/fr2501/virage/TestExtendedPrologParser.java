package com.fr2501.virage;

import static org.junit.Assert.assertTrue;

import java.io.File;
import java.io.FileNotFoundException;

import org.junit.Test;

import com.fr2501.virage.prolog.ExtendedPrologParser;
import com.fr2501.virage.prolog.SimpleExtendedPrologParser;

public class TestExtendedPrologParser {
	@Test(expected = FileNotFoundException.class)
	public void loadInvalidFile() {
		ExtendedPrologParser parser = new SimpleExtendedPrologParser();
		
		parser.parseFramework(new File(""));
	}
	
	@Test
	public void loadValidFile() {
		ExtendedPrologParser parser = new SimpleExtendedPrologParser();
		
		parser.parseFramework(new File("test/resources/test.pl"));
	}
	
	@Test
	public void loadFrameworkFile() {
		ExtendedPrologParser parser = new SimpleExtendedPrologParser();
		
		parser.parseFramework(new File("test/resources/framework.pl"));
	}
	
	@Test(expected = IllegalArgumentException.class)
	public void parseEmptyClause() {
		String clause = "";
		ExtendedPrologParser parser = new SimpleExtendedPrologParser();
		
		parser.parseSingleClause(clause);
	}
	
	@Test
	public void parseSingleClause() {
		String clause = "a :- b, c.";
		ExtendedPrologParser parser = new SimpleExtendedPrologParser();
		
		String res = parser.parseSingleClause(clause).toString();
		
		assertTrue(clause.equals(res));
	}
}
