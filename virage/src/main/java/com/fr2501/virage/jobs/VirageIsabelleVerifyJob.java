package com.fr2501.virage.jobs;

import java.io.File;

import com.fr2501.virage.core.VirageUserInterface;
import com.fr2501.virage.isabelle.IsabelleProofChecker;

public class VirageIsabelleVerifyJob extends VirageJobWithExplicitResult<Boolean> {
	private IsabelleProofChecker checker;
	
	private File file;

	public VirageIsabelleVerifyJob(VirageUserInterface issuer, File file) {
		super(issuer);
		
		this.file = file;
	}
	
	@Override
	protected void concreteExecute() throws Exception {
		this.checker = this.executingCore.getIsabelleProofChecker();
		
		this.result = this.checker.verifyTheoryFile(this.file.getAbsolutePath());
	}

}
