package com.fr2501.virage.isabelle;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStream;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;


/**
 * 
 * This class connects ViRAGe to Isabelle and automatically invokes
 * the Isabelle processes required to attempt automatic proof verification.
 * It is meant to be a singleton, as every instance would spawn new processes.
 *
 */
public class IsabelleProofChecker {
	private static IsabelleProofChecker instance = null;
	private static final String SERVER_NAME = "virage_isabelle_server";
	
	private static final Logger logger = LogManager.getLogger(IsabelleProofChecker.class);
	
	private Runtime runtime;
	private Process server;
	private Process client;
	private OutputStream clientInput;
	private String sessionId;
	
	boolean finished = false;
	IsabelleEvent lastEvent;
	
	private IsabelleProofChecker() {
		this.runtime = Runtime.getRuntime();
		
		try {
			this.initServer();
			this.initClient();
		} catch (IOException e) {
			logger.error("Something went wrong.", e);
			e.printStackTrace();
		}
	}
	
	private synchronized boolean getFinished() {
		return this.finished;
	}
	
	public synchronized void setFinished(boolean finished) {
		this.finished = finished;
	}
	
	/**
	 * Creates singleton instance, if necessary, and returns it.
	 * 
	 * @return the instance
	 */
	public static IsabelleProofChecker getInstance() {
		if(instance == null) {
			instance = new IsabelleProofChecker();
		}
		
		return instance;
	}
	
	/**
	 * Attempts to automatically verify the given Isabelle theory
	 * @param theory qualifying name for (or path to) an Isabelle theory file
	 * @return true if verification succeeds, false otherwise
	 * 
	 * @throws IOException if file system interaction fails
	 * @throws InterruptedException if execution is interrupted by the OS
	 */
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
	
	/**
	 * Destroys the current instance and its associated Isabelle processes
	 */
	public void destroy() {
		this.client.destroy();
		this.server.destroy();
		
		instance = null;
	}
	
	/**
	 * Applies the effects of a given event.
	 * @param evt the event
	 */
	public void notify(IsabelleEvent evt) {
		logger.debug(evt.toString());
		this.lastEvent = evt;
		evt.applyEffects(this);
	}
	
	private void sendCommandAndWaitForTermiantion(String command) throws IOException {
		this.clientInput.write((command + "\n").getBytes());
		this.clientInput.flush();
		
		this.waitForFinish();
	}
	
	private void initServer() throws IOException {
		this.server = this.runtime.exec("isabelle server -n " + SERVER_NAME);
		
		// The server will send a message when startup is finished.
		// Contents are irrelevant, just wait for it to appear.
		BufferedReader reader = new BufferedReader(new InputStreamReader(this.server.getInputStream()));
		while(!reader.ready());
	}
	
	private void initClient() throws IOException {
		this.client = this.runtime.exec("isabelle client -n " + SERVER_NAME);
		this.clientInput = this.client.getOutputStream();
		
		IsabelleClientObserver.start(this, this.client);
		
		this.sendCommandAndWaitForTermiantion("session_start {\"session\": \"HOL\"}");
		this.sessionId = this.lastEvent.getValue("session_id");
	}
	
	private void waitForFinish() {
		while(!this.getFinished());
		this.finished = false;
	}
}
