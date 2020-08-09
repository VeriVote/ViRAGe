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

import com.fr2501.util.Pair;
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
	 * Attempts to automatically verify the given Isabelle theory. Might move the theory to a new file
	 * in the process because Isabelle purge_theories does not actually lead to reloading if the theory
	 * is used again and in the same file (might be a bug?).
	 * 
	 * @param path to an Isabelle theory file
	 * @return (true, newFile) if verification succeeds, (false, null) otherwise
	 * 
	 * @throws IOException if file system interaction fails
	 * @throws InterruptedException if execution is interrupted by the OS
	 */
	public Pair<Boolean,File> verifyTheoryFile(File theory) throws IOException, InterruptedException {
		String theoryPath = theory.getCanonicalPath();
		
		if(theoryPath.endsWith(IsabelleUtils.FILE_EXTENSION)) {
			theoryPath = theoryPath.substring(0,theoryPath.length() - IsabelleUtils.FILE_EXTENSION.length());
		}
		
		logger.info("Starting to verify " + theory + ". This might take some time.");
		String command = "use_theories {\"session_id\": \"" + this.sessionId + "\", " +
				"\"theories\": [\"" + theoryPath + "\"]}";  
		this.sendCommandAndWaitForTermination(command);
		
		String result = this.lastEvent.getValue("ok");
		if(result.equals("true")) {
			logger.info("Verification successful.");
			return new Pair<Boolean,File>(true,theory);
		} else {
			logger.info("Verification failed. Attempting to solve automatically by employing different solvers.");
			String errors = this.lastEvent.getValue("errors");
			
			command = "purge_theories {\"session_id\": \"" + this.sessionId + "\", " +
					"\"theories\": [\"" + theoryPath + "\"]}";  
			this.sendCommandAndWaitForOk(command);
			
			Pattern pattern = Pattern.compile("line=[0-9]+");
			Matcher matcher = pattern.matcher(errors);
			
			if(matcher.find()) {
				String line = errors.substring(matcher.start(), matcher.end());
				// Isabelle starts counting at 1.
				int lineNum = Integer.parseInt(line.split("=")[1]) - 1;
		
				File newFile = this.replaceSolver(theory, lineNum);
				if(newFile != null) {
					// The content of the file has changed, and this can
					// only happen IsabelleUtils.SOLVERS.length times,
					// so the recursive call is fine.
					return this.verifyTheoryFile(newFile);
				}
			}
			
			return new Pair<Boolean,File>(false, null);
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
	
	// This is the simplest, and probably slowest, solution to the problem that some composition
	// rules can only be solved by certain solvers, essentially brute-forcing it.
	// Claim: If a proof method solves a step using a certain composition rule *once*, it will
	// solve *all* steps that only use this rule. TODO: Investigate that.
	private File replaceSolver(File theory, int lineNum) {
		//return false;
		
		SimpleFileReader reader = new SimpleFileReader();
		SimpleFileWriter writer = new SimpleFileWriter();
		
		try {
			List<String> lines = reader.readFileByLine(theory);
			String theoryPath = theory.getCanonicalPath();
			
			Pattern pattern = Pattern.compile("_v[0-9]+" + IsabelleUtils.FILE_EXTENSION);
			Matcher matcher = pattern.matcher(theoryPath);
			
			int fileVersion = 1;
			String theoryPathWithoutSuffix = theoryPath.substring(0,theoryPath.length() - 4);
			if(matcher.find()) {
				String fileVersionString = theoryPath.substring(matcher.start()+2, matcher.end()-4);
				fileVersion = Integer.parseInt(fileVersionString) + 1;
				
				theoryPathWithoutSuffix = theoryPathWithoutSuffix.substring(0,matcher.start());
			}
			
			
			String theoryName = theory.getName().substring(0,theory.getName().length()-4);
			String newTheoryPath = theoryPathWithoutSuffix + "_v" + fileVersion + IsabelleUtils.FILE_EXTENSION;
			
			String[] splits = newTheoryPath.split(File.separator);
			String newTheoryName = splits[splits.length-1].substring(0,splits[splits.length-1].length()-4);
			
			String line = lines.get(lineNum);
			
			for(int i=0; i<IsabelleUtils.SOLVERS.length-1; i++) {
				if(line.contains(IsabelleUtils.SOLVERS[i])) {
					line = line.replace(IsabelleUtils.SOLVERS[i], IsabelleUtils.SOLVERS[i+1]);
					
					lines.set(lineNum, line);
					
					String result = "";
					for(String s: lines) {
						if(s.contains(theoryName)) {
							s = s.replace(theoryName, newTheoryName);
						}
						
						result += s + "\n";
					}
					
					theory.delete();
					writer.writeToFile(newTheoryPath, result);
					
					return new File(newTheoryPath);
				}
			}

			return null;			
		} catch (IOException e) {
			throw new IllegalArgumentException();
		}
	}
}
