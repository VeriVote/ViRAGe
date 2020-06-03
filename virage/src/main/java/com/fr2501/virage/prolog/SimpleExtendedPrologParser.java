package com.fr2501.virage.prolog;

import java.io.File;
import java.util.List;

import com.fr2501.util.SimpleFileReader;
import com.fr2501.virage.types.FrameworkRepresentation;

public class SimpleExtendedPrologParser implements ExtendedPrologParser {
	SimpleFileReader fileReader;
	PrologParser prologParser;
	
	public SimpleExtendedPrologParser() {
		this.fileReader = new SimpleFileReader();
		this.prologParser = new SimplePrologParser();
	}
	
	@Override
	public FrameworkRepresentation parseFramework(File file) {
		List<String> framework = this.fileReader.readFileByLine(file);
		
		return this.parseFramework(framework);
	}

	@Override
	public FrameworkRepresentation parseFramework(List<String> representation) {
		FrameworkRepresentation framework = new FrameworkRepresentation();
		
		
		
		return framework;
	}
}
