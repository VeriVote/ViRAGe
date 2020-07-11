package com.fr2501.virage.jobs;

import com.fr2501.virage.core.VirageUserInterface;
import com.fr2501.virage.types.FrameworkRepresentation;

/**
 *
 * A {@link VirageJob} requiring an executor and a given {@link FrameworkRepresentation}
 *
 * @param <S> the type of the executor
 * @param <T> the result type
 */
public abstract class VirageExecutorJobWithFramework<S,T> extends VirageExecutorJob<S,T> {
	protected boolean hasFramework = false;
	protected FrameworkRepresentation framework;
	
	public VirageExecutorJobWithFramework(VirageUserInterface issuer) {
		super(issuer);
	}
	
	/**
	 * Must be called before execution, attaches a {@link FrameworkRepresentation} to the job.
	 * @param framework the framework
	 */
	public void addFramework(FrameworkRepresentation framework) {
		this.framework = framework;
		this.hasFramework = true;
	}
	
	@Override
	public boolean isReadyToExecute() {
		return this.hasExecutor && this.hasFramework;
	}
}
