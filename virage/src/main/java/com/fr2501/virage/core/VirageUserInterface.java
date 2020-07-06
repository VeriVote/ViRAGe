package com.fr2501.virage.core;

import java.util.List;

// TODO: Document
public interface VirageUserInterface extends Runnable {
	public void init();
	public boolean hasJobs();
	public VirageJob getJob() throws InterruptedException;
}
