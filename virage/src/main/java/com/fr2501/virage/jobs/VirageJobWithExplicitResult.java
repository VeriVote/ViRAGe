package com.fr2501.virage.jobs;

import com.fr2501.virage.core.VirageUserInterface;

public abstract class VirageJobWithExplicitResult<T> extends VirageJob<T> {
	protected T result;
	
	public VirageJobWithExplicitResult(VirageUserInterface issuer) {
		super(issuer);
	}
	
	public T getResult() {
		return this.result;
	}

	@Override
	public String toString() {
		String res = super.toString();
		
		res += "Result: " + this.result.toString() + "\n";
		
		return res;
	}
}
