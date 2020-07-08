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

public class VirageCommandLineInterface implements VirageUserInterface {
	private static final Logger logger = LogManager.getLogger(VirageCommandLineInterface.class);
	private Scanner scanner;
	
	private BlockingQueue<VirageJob> jobs;
	
	private Thread thread;
		
	@Override
	public void run() {
		logger.info("Started VirageCommandLineInterface.");
		
		System.out.println("Please input the absolute path to an EPL file.");
		String path = this.scanner.nextLine();
		
		this.jobs.add(new VirageParseJob(new File(path)));
		
		while(true) {
			System.out.println("Do you want to (g)enerate a composition or (a)nalyze one?");
			String arg = this.scanner.nextLine();
			if(arg.equals("g")) {
				this.createGenerationQuery();
			} else if(arg.equals("a")) {
				this.createAnalysisQuery();
			} else if(arg.equals("exit")) {
				this.jobs.add(new VirageExitJob(0));
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
		
		this.jobs.add(new VirageGenerateJob(properties));
	}
	
	private void createAnalysisQuery() {
		System.out.println("Please input a composition (in Prolog format).");
		String composition = this.scanner.nextLine();
		
		System.out.println("Please input the desired properties (separated by ',').");
		String propertyString = this.scanner.nextLine();

		List<String> properties = StringUtils.separate(",", propertyString);
		
		this.jobs.add(new VirageAnalyzeJob(composition, properties));
	}
	
	@Override
	public void init() {
		logger.info("Initialising VirageCommandLineInterface.");
		
		this.scanner = new Scanner(System.in);
		
		this.jobs = new LinkedBlockingQueue<VirageJob>();
		
		this.thread = new Thread(this, "vcli");
		this.thread.start();
	}

	@Override
	public boolean hasJobs() {	
		return !(this.jobs.isEmpty());
	}

	@Override
	public VirageJob getJob() throws InterruptedException {
		return this.jobs.take();
	}
}
