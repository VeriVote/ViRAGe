package com.fr2501.virage.core;

// TODO: Document
public abstract class VirageJob {
	protected VirageJobState state;
	
	public VirageJob() {
		this.state = VirageJobState.PENDING;
	}
	
	public abstract void execute();
	
	public boolean isReadyToExecute() {
		return true;
	}
	
	public VirageJobState getState() {
		return this.state;
	}
	
	public void setState(VirageJobState state) {
		this.state = state;
	}
}
