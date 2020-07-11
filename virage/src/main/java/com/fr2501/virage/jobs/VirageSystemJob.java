package com.fr2501.virage.jobs;

import com.fr2501.virage.core.VirageUserInterface;

/**
 * 
 * A special type of {@link VirageJob}, they are executed instantly on submission.
 *
 * @param <T> the result type
 */
public abstract class VirageSystemJob<T> extends VirageJob<T> {
	public VirageSystemJob(VirageUserInterface issuer) {
		super(issuer);
	}
}
