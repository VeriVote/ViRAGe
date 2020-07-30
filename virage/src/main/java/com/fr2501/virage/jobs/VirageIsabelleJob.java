package com.fr2501.virage.jobs;

import java.util.List;

import com.fr2501.virage.core.VirageUserInterface;
import com.fr2501.virage.isabelle.IsabelleTheoryGenerator;
import com.fr2501.virage.types.CompositionProof;

// TODO: Document
public class VirageIsabelleJob extends VirageJobWithoutExplicitResult {
	private String composition;
	private List<CompositionProof> proofs;
	
	private IsabelleTheoryGenerator generator;

	public VirageIsabelleJob(VirageUserInterface issuer, String composition,
			List<CompositionProof> proofs) {
		super(issuer);
		
		this.composition = composition;
		this.proofs = proofs;
	}

	@Override
	protected void concreteExecute() throws Exception {
		this.generator = this.executingCore.getIsabelleTheoryGenerator();
		
		this.generator.generateTheoryFile(this.executingCore.getFrameworkRepresentation().getTheoryPath(), 
				this.composition, this.proofs);
	}
}
