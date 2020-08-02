package com.fr2501.virage.isabelle;

import java.io.IOException;
import java.io.OutputStream;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;


// TODO: Document
public class IsabelleProofChecker {
	private static IsabelleProofChecker instance = null;
	private static final String SERVER_NAME = "virage_isabelle_server";
	
	long timeout = 60000;
	
	private static final Logger logger = LogManager.getLogger(IsabelleProofChecker.class);
	
	private Runtime runtime;
	private Process server;
	private Process client;
	private IsabelleClientObserver observer;
	private OutputStream clientInput;
	String sessionId;
	
	boolean finished = false;
	IsabelleEvent lastEvent;
	
	private IsabelleProofChecker() {
		this.runtime = Runtime.getRuntime();
		
		try {
			this.initServer();
			this.initClient();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}
	
	public static IsabelleProofChecker getInstance() {
		if(instance == null) {
			instance = new IsabelleProofChecker();
		}
		
		return instance;
	}
	
	public boolean verifyTheoryFile(String theory) throws IOException, InterruptedException {
		if(theory.endsWith(".thy")) {
			theory = theory.substring(0,theory.length() - ".thy".length());
		}
		
		logger.info("Starting to verify " + theory + ". This might take some time.");
		String command = "use_theories {\"session_id\": \"" + this.sessionId + "\", " +
				"\"theories\": [\"" + theory + "\"]}";  
		this.sendCommandAndWaitForTermiantion(command);
		
		String result = this.lastEvent.getValue("ok");
		if(result.equals("true")) {
			logger.info("Verification successful.");
			return true;
		} else {
			logger.info("Verification failed. You might be able to fix the errors manually within Isabelle.");
			return false;
		}
	}
	
	public void destroy() {
		this.client.destroy();
		this.server.destroy();
	}
	
	private void sendCommandAndWaitForTermiantion(String command) throws IOException {
		this.clientInput.write((command + "\n").getBytes());
		this.clientInput.flush();
		
		this.waitForFinish();
	}
	
	private void initServer() throws IOException {
		this.server = this.runtime.exec("isabelle server -n " + SERVER_NAME);
		// TODO: Check success?
	}
	
	private void initClient() throws IOException {
		this.client = this.runtime.exec("isabelle client -n " + SERVER_NAME);
		this.clientInput = this.client.getOutputStream();
		
		this.observer = new IsabelleClientObserver(this, this.client);
		
		this.sendCommandAndWaitForTermiantion("session_start {\"session\": \"HOL\"}");
		this.sessionId = this.lastEvent.getValue("session_id");
	}
	
	private void waitForFinish() {
		while(!this.getFinished());
		this.finished = false;
	}
	
	private synchronized boolean getFinished() {
		return this.finished;
	}
	
	public synchronized void setFinished(boolean finished) {
		this.finished = finished;
	}

	
	public void notify(IsabelleEvent evt) {
		logger.debug(evt.toString());
		this.lastEvent = evt;
		evt.applyEffects(this);
	}
}
