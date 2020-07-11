package com.fr2501.virage.jobs;

import com.fr2501.virage.core.VirageUserInterface;

/**
 * 
 * A {@link VirageJob} requiring another object for execution.
 *
 * @param <S> the type of the executing object
 * @param <T> the type of the job's result
 */
public abstract class VirageExecutorJob<S,T> extends VirageJob<T> {
	protected S executor;
	
	protected boolean hasExecutor = false;
	
	public VirageExecutorJob(VirageUserInterface issuer) {
		super(issuer);
	}
	
	/**
	 * Must be called before execution, attaches an executing object to the job.
	 * @param executor the executing object
	 */
	public void attachExecutor(S executor) {
		this.executor = executor;
		
		this.hasExecutor = true;
	}
	
	@Override
	public boolean isReadyToExecute() {
		return this.hasExecutor;
	}
	
	@Override
	public String toString() {
		String res = super.toString();
		
		String resultString = "null";
		if(this.getResult() != null) {
			resultString = this.getResult().toString();
		}
		res += "Result: " + resultString;
		
		return res;
	}
}
