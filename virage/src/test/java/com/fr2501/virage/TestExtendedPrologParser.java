package com.fr2501.virage;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.IOException;

import org.junit.Test;

import com.fr2501.virage.prolog.ExtendedPrologParser;
import com.fr2501.virage.prolog.MalformedEPLFileException;
import com.fr2501.virage.prolog.SimpleExtendedPrologParser;

public class TestExtendedPrologParser {
	@Test(expected = FileNotFoundException.class)
	public void loadNonExistingFile() throws IOException, MalformedEPLFileException {
		ExtendedPrologParser parser = new SimpleExtendedPrologParser();
		
		parser.parseFramework(new File(""));	
	}
	
	@Test(expected = MalformedEPLFileException.class)
	public void loadInvalidFile() throws IOException, MalformedEPLFileException {
		ExtendedPrologParser parser = new SimpleExtendedPrologParser();
		
		parser.parseFramework(new File("src/test/resources/invalid_test.pl"));	
	}
	
	@Test
	public void loadValidFile() throws IOException, MalformedEPLFileException {
		ExtendedPrologParser parser = new SimpleExtendedPrologParser();
		
		parser.parseFramework(new File("src/test/resources/valid_test.pl"));
	}
	
	@Test
	public void loadFrameworkFile() throws IOException, MalformedEPLFileException {
		ExtendedPrologParser parser = new SimpleExtendedPrologParser();
		
		parser.parseFramework(new File("src/main/resources/framework.pl"));
	}
}
