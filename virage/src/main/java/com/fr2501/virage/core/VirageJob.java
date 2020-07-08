package com.fr2501.virage.core;

// TODO: Document
public abstract class VirageJob {
	protected VirageJobState state;
	
	public VirageJob() {
		this.state = VirageJobState.PENDING;
	}
	
	public abstract void execute();
	
	public boolean requiresExecutor() {
		return false;
	}
	
	public boolean requiresFramework() {
		return false;
	}
	
	public boolean isReadyToExecute() {
		return true;
	}
	
	public VirageJobState getState() {
		return this.state;
	}
}
