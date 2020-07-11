package com.fr2501.virage.jobs;

import java.io.File;
import java.io.IOException;

import com.fr2501.virage.core.VirageUserInterface;
import com.fr2501.virage.prolog.ExtendedPrologParser;
import com.fr2501.virage.prolog.MalformedEPLFileException;
import com.fr2501.virage.types.FrameworkRepresentation;

/**
 * 
 * A {@link VirageJob} used to parse an extended Prolog file.
 *
 */
public class VirageParseJob extends VirageExecutorJob<ExtendedPrologParser, FrameworkRepresentation> {
	private FrameworkRepresentation framework;
	
	private File file;
	
	public VirageParseJob(VirageUserInterface issuer, File file) {
		super(issuer);
		
		this.file = file;
	}
	
	@Override
	public void concreteExecute() throws IOException, MalformedEPLFileException {
		this.framework = this.executor.parseFramework(this.file);
	}

	@Override
	public FrameworkRepresentation getResult() {
		return this.framework;
	}
}
