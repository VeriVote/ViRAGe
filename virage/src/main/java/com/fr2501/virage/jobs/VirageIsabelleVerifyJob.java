package com.fr2501.virage.jobs;

import java.io.File;

import com.fr2501.util.Pair;
import com.fr2501.virage.core.VirageUserInterface;
import com.fr2501.virage.isabelle.IsabelleProofChecker;

/**
 * 
 * A {@link VirageJob} that invokes Isabelle to automatically attempt proof verification.
 *
 */
public class VirageIsabelleVerifyJob extends VirageJobWithExplicitResult<Pair<Boolean,File>> {
	private IsabelleProofChecker checker;
	
	private File file;

	public VirageIsabelleVerifyJob(VirageUserInterface issuer, File file) {
		super(issuer);
		
		this.file = file;
	}
	
	@Override
	protected void concreteExecute() throws Exception {
		this.checker = this.executingCore.getIsabelleProofChecker();
		
		this.result = this.checker.verifyTheoryFile(this.file);
	}

}
