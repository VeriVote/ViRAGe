package com.fr2501.virage.core;

import java.util.LinkedList;
import java.util.List;
import java.util.Queue;
import java.util.Scanner;
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
		
		this.jobs.add(new VirageJob(VirageJobType.PARSE_EPL, path));
		
		while(true) {
			System.out.println("Do you want to (g)enerate a composition or (a)nalyze one?");
			String arg = this.scanner.nextLine();
			if(arg.equals("g")) {
				this.createGenerationQuery();
			} else if(arg.equals("a")) {
				
			} else {
				System.out.println("Please try again.");
				continue;
			}
		}
	}
	
	private void createGenerationQuery() {
		System.out.println("Please input the desired properties (separated by ',').");
		String propertyString = this.scanner.nextLine();
		propertyString = StringUtils.removeWhitespace(propertyString);
		
		this.jobs.add(new VirageJob(VirageJobType.GENERATE, propertyString));
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
