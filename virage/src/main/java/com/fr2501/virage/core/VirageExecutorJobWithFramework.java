package com.fr2501.virage.core;

import com.fr2501.virage.types.FrameworkRepresentation;

// TODO Document
public abstract class VirageExecutorJobWithFramework<S,T> extends VirageExecutorJob<S,T> {
	protected boolean hasFramework = false;
	protected FrameworkRepresentation framework;
	
	public void addFramework(FrameworkRepresentation framework) {
		this.framework = framework;
		this.hasFramework = true;
	}
	
	@Override
	public boolean isReadyToExecute() {
		return this.hasExecutor && this.hasFramework;
	}
}
