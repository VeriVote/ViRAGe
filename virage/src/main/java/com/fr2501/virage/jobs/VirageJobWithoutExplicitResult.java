package com.fr2501.virage.jobs;

import com.fr2501.virage.core.VirageUserInterface;

public abstract class VirageJobWithoutExplicitResult extends VirageJob<Void> {
	public VirageJobWithoutExplicitResult(VirageUserInterface issuer) {
		super(issuer);
	}

	@Override
	public Void getResult() {
		throw new UnsupportedOperationException();
	}
}
