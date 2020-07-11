package com.fr2501.virage.core;

import java.io.File;

import com.fr2501.virage.jobs.VirageExecutorJob;
import com.fr2501.virage.prolog.ExtendedPrologParser;
import com.fr2501.virage.types.FrameworkRepresentation;

//TODO Document
public class VirageParseJob extends VirageExecutorJob<ExtendedPrologParser, FrameworkRepresentation> {
	private FrameworkRepresentation framework;
	
	private File file;
	
	public VirageParseJob(File file) {
		this.file = file;
	}
	
	@Override
	public void execute() {
		try {
			this.framework = this.executor.parseFramework(this.file);
			this.state = VirageJobState.FINISHED;
		} catch (Exception e) {
			this.state = VirageJobState.FAILED;
		}
	}

	@Override
	public FrameworkRepresentation getResult() {
		return this.framework;
	}
}
