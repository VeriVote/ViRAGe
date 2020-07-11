package com.fr2501.virage.jobs;

// TODO Document
public class VirageExitJob extends VirageSystemJob {
	private int statusCode;
	
	public VirageExitJob(int statusCode) {
		this.statusCode = statusCode;
	}
	
	@Override
	public void execute() {
		System.exit(this.statusCode);
	}	
}
