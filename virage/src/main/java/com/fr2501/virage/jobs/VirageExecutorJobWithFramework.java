package com.fr2501.virage.jobs;

import com.fr2501.virage.core.VirageUserInterface;
import com.fr2501.virage.types.FrameworkRepresentation;

// TODO Document
public abstract class VirageExecutorJobWithFramework<S,T> extends VirageExecutorJob<S,T> {
	protected boolean hasFramework = false;
	protected FrameworkRepresentation framework;
	
	public VirageExecutorJobWithFramework(VirageUserInterface issuer) {
		super(issuer);
	}
	
	public void addFramework(FrameworkRepresentation framework) {
		this.framework = framework;
		this.hasFramework = true;
	}
	
	@Override
	public boolean isReadyToExecute() {
		return this.hasExecutor && this.hasFramework;
	}
}
