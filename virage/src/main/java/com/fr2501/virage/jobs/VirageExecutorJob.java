package com.fr2501.virage.jobs;

import com.fr2501.virage.core.VirageJob;

// TODO Document
public abstract class VirageExecutorJob<S,T> extends VirageJob {
	protected S executor;
	
	protected boolean hasExecutor = false;
	
	public abstract T getResult();
	
	public void attachExecutor(S executor) {
		this.executor = executor;
		
		this.hasExecutor = true;
	}
	
	@Override
	public boolean isReadyToExecute() {
		return this.hasExecutor;
	}
}
