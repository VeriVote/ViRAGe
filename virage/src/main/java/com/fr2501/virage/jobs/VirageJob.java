package com.fr2501.virage.jobs;

import java.time.Instant;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import com.fr2501.virage.core.VirageUserInterface;

// TODO: Document
public abstract class VirageJob<T> {
	private static final Logger logger = LogManager.getLogger(VirageJob.class);
	private VirageUserInterface issuer;
	
	protected VirageJobState state;
	
	private static long next_id = 0;
	
	private long id;
	
	private long time_issued;
	private long time_started;
	private long time_finished;
	
	public VirageJob(VirageUserInterface issuer) {
		this.issuer = issuer;
		this.id = VirageJob.next_id;
		VirageJob.next_id++;
		
		this.time_issued = System.currentTimeMillis();
		
		this.state = VirageJobState.PENDING;
	}
	
	public void execute() {
		this.setState(VirageJobState.RUNNING);
		
		try {
			this.concreteExecute();
			this.setState(VirageJobState.FINISHED);
		} catch(Exception e) {
			logger.error("An error occured." ,e);
			this.setState(VirageJobState.FAILED);
		}
		
		this.issuer.notify(this);
	}
	
	protected abstract void concreteExecute() throws Exception;
	
	public boolean isReadyToExecute() {
		return true;
	}
	
	public abstract T getResult();
	
	public VirageJobState getState() {
		return this.state;
	}
	
	public void setState(VirageJobState state) {
		if(state == VirageJobState.RUNNING) {
			this.time_started = System.currentTimeMillis();
		} else if(state == VirageJobState.FAILED || state == VirageJobState.FINISHED) {
			this.time_finished = System.currentTimeMillis();
		}
		
		this.state = state;
	}
	
	@Override
	public String toString() {
		String res = "----------- " + this.getClass().getCanonicalName() + "\n";
		res += "ID: " + this.id + "\n";
		
		res += "Issued: " + Instant.ofEpochMilli(time_issued).toString() + "\n";
		res += "Started: " + Instant.ofEpochMilli(time_started).toString() + "\n";
		res += "Finished: " + Instant.ofEpochMilli(time_finished).toString() + "\n";
		res += "-----\n";
		res += "State: " + this.state + "\n";
	
		return res;
	}
}
