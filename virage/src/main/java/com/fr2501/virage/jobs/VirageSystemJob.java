package com.fr2501.virage.jobs;

import com.fr2501.virage.core.VirageUserInterface;

//TODO: Document
public abstract class VirageSystemJob<T> extends VirageJob<T> {
	public VirageSystemJob(VirageUserInterface issuer) {
		super(issuer);
	}
}
