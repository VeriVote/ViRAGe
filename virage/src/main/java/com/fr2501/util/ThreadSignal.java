package com.fr2501.util;

// TODO: DOC
public class ThreadSignal {
	private boolean finished = false;
	
	private synchronized boolean getFinished() {
		return this.finished;
	}
	
	public synchronized void finish() {
		this.finished = true;
	}
	
	public void waitFor() {
		while(!this.getFinished()) { /* no-op */ };
	}
}
