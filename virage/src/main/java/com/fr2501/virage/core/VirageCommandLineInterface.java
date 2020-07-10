package com.fr2501.virage.core;

import java.io.File;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Queue;
import java.util.Scanner;
import java.util.Set;
import java.util.concurrent.BlockingQueue;
import java.util.concurrent.LinkedBlockingQueue;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import com.fr2501.util.StringUtils;

// TODO Document
public class VirageCommandLineInterface implements VirageUserInterface {
	private static final Logger logger = LogManager.getLogger(VirageCommandLineInterface.class);
	private Scanner scanner;
	private VirageCore core;
	
	private Thread thread;
	
	protected VirageCommandLineInterface(VirageCore core) {
		logger.info("Initialising VirageCommandLineInterface.");
		
		this.scanner = new Scanner(System.in);
		this.core = core;
		
		this.thread = new Thread(this, "vcli");
		this.thread.start();
	}
		
	@Override
	public void run() {
		logger.info("Started VirageCommandLineInterface.");
		
		System.out.println("Please input the absolute path to an EPL file.");
		String path = this.scanner.nextLine();
		
		this.core.submit(new VirageParseJob(new File(path)));
		
		while(true) {
			System.out.println("Do you want to (g)enerate a composition or (a)nalyze one?");
			String arg = this.scanner.nextLine();
			if(arg.equals("g")) {
				this.createGenerationQuery();
			} else if(arg.equals("a")) {
				this.createAnalysisQuery();
			} else if(arg.equals("exit")) {
				this.core.submit(new VirageExitJob(0));
				return;
			} else {
				System.out.println("Please try again.");
				continue;
			}
		}
	}
	
	private void createGenerationQuery() {
		System.out.println("Please input the desired properties (separated by ',').");
		String propertyString = this.scanner.nextLine();

		List<String> properties = StringUtils.separate(",", propertyString);
		
		this.core.submit(new VirageGenerateJob(properties));
	}
	
	private void createAnalysisQuery() {
		System.out.println("Please input a composition (in Prolog format).");
		String composition = this.scanner.nextLine();
		
		System.out.println("Please input the desired properties (separated by ',').");
		String propertyString = this.scanner.nextLine();

		List<String> properties = StringUtils.separate(",", propertyString);
		
		this.core.submit(new VirageAnalyzeJob(composition, properties));
	}
}
