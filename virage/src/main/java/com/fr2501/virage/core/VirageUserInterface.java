package com.fr2501.virage.core;

import com.fr2501.virage.jobs.VirageJob;

/**
 * 
 * Interface specifying requirements for all user interfaces of ViRAGe.
 *
 */
public interface VirageUserInterface extends Runnable {
	public void launch();
	
	public void notify(VirageJob<?> job);
}
