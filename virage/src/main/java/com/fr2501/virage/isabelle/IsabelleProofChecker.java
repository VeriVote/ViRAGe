package com.fr2501.virage.isabelle;

import java.io.BufferedReader;
import java.io.File;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStream;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import com.fr2501.util.SimpleFileReader;
import com.fr2501.util.SimpleFileWriter;


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
		this.sendCommandAndWaitForTermination(command);
		
		String result = this.lastEvent.getValue("ok");
		if(result.equals("true")) {
			logger.info("Verification successful.");
			return true;
		} else {
			logger.info("Verification failed. Attempting to solve automatically by employing different solvers.");
			String errors = this.lastEvent.getValue("errors");
			
			command = "purge_theories {\"session_id\": \"" + this.sessionId + "\", " +
					"\"theories\": [\"" + theory + "\"]}";  
			this.sendCommandAndWaitForOk(command);
			
			Pattern pattern = Pattern.compile("line=[0-9]+");
			Matcher matcher = pattern.matcher(errors);
			
			if(matcher.find()) {
				String line = errors.substring(matcher.start(), matcher.end());
				// Isabelle starts counting at 1.
				int lineNum = Integer.parseInt(line.split("=")[1]) - 1;
			
				if(this.replaceSolver(theory, lineNum)) {
					// The content of the file has changed, and this can
					// only happen IsabelleUtils.SOLVERS.length times,
					// so the recursive call is fine.
					return this.verifyTheoryFile(theory);
				}
			}
			
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
	public synchronized void notify(IsabelleEvent evt) {
		logger.debug(evt.toString());
		this.lastEvent = evt;
		evt.applyEffects(this);
	}
	
	private synchronized IsabelleEvent getLastEvent() {
		return this.lastEvent;
	}
	
	private void sendCommandAndWaitForTermination(String command) throws IOException {
		this.clientInput.write((command + "\n").getBytes());
		this.clientInput.flush();
		
		this.waitForFinish();
	}
	
	private void sendCommandAndWaitForOk(String command) throws IOException {
		this.clientInput.write((command + "\n").getBytes());
		this.clientInput.flush();
		
		// TODO: There is probably a better solution for this.
		while(!(this.getLastEvent() instanceof IsabelleOkEvent)) {
			
		}
		
		this.lastEvent = new IsabelleMiscEvent();
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
		
		this.sendCommandAndWaitForTermination("session_start {\"session\": \"HOL\"}");
		this.sessionId = this.lastEvent.getValue("session_id");
	}
	
	private void waitForFinish() {
		while(!this.getFinished());
		this.finished = false;
	}
	
	// TODO: This feature would be really nice to have, but even purging and reusing theories
	// does not make Isabelle actually reload them, so this is infeasible for now.
	private boolean replaceSolver(String theoryPath, int lineNum) {
		return false;
		
		/*SimpleFileReader reader = new SimpleFileReader();
		SimpleFileWriter writer = new SimpleFileWriter();
		
		String filePath = theoryPath + IsabelleUtils.FILE_EXTENSION;
		
		try {
			List<String> lines = reader.readFileByLine(new File(filePath));
			
			String line = lines.get(lineNum);
			
			for(int i=0; i<IsabelleUtils.SOLVERS.length-1; i++) {
				if(line.contains(IsabelleUtils.SOLVERS[i])) {
					line = line.replace(IsabelleUtils.SOLVERS[i], IsabelleUtils.SOLVERS[i+1]);
					
					lines.set(lineNum, line);
					
					String result = "";
					for(String s: lines) {
						result += s + "\n";
					}
					
					writer.writeToFile(filePath, result);
					
					return true;
				}
			}

			return false;			
		} catch (IOException e) {
			// TODO: Auto-generated catch block
			return false;
		}
	}*/
}
