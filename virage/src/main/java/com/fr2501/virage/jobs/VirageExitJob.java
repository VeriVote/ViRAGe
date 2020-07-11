package com.fr2501.virage.jobs;

import com.fr2501.virage.core.VirageUserInterface;

// TODO Document
public class VirageExitJob extends VirageSystemJob {
	private int statusCode;
	
	
	public VirageExitJob(VirageUserInterface issuer, int statusCode) {
		super(issuer);
		
		this.statusCode = statusCode;
	}
	
	@Override
	public void concreteExecute() {
		System.exit(this.statusCode);
	}	
}
