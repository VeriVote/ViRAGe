package com.fr2501.virage.core;

import java.io.IOException;
import java.util.concurrent.BlockingQueue;
import java.util.concurrent.LinkedBlockingQueue;

import org.apache.commons.cli.CommandLine;
import org.apache.commons.cli.CommandLineParser;
import org.apache.commons.cli.DefaultParser;
import org.apache.commons.cli.HelpFormatter;
import org.apache.commons.cli.Option;
import org.apache.commons.cli.OptionBuilder;
import org.apache.commons.cli.Options;
import org.apache.commons.cli.ParseException;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import com.fr2501.virage.analyzer.AdmissionCheckPrologCompositionAnalyzer;
import com.fr2501.virage.analyzer.SimplePrologCompositionAnalyzer;
import com.fr2501.virage.isabelle.IsabelleTheoryGenerator;
import com.fr2501.virage.jobs.VirageJob;
import com.fr2501.virage.prolog.ExtendedPrologParser;
import com.fr2501.virage.prolog.SimpleExtendedPrologParser;
import com.fr2501.virage.types.FrameworkRepresentation;

/**
 * 
 * The main application
 *
 */

// This is required due to Commons CLI still recommending the deprecated way of building Options.
@SuppressWarnings("deprecation")
public class VirageCore implements Runnable {
	private final static Logger logger = LogManager.getLogger(VirageCore.class.getName());
	
	private CommandLine cl;
	private String[] args;
	private VirageUserInterface ui;
	
	private ExtendedPrologParser extendedPrologParser = null;
	private VirageSearchManager searchManager = null;
	private IsabelleTheoryGenerator generator = null;
	private FrameworkRepresentation framework = null;
	
	private BlockingQueue<VirageJob<?>> jobs;

    public VirageCore(String[] args) throws ParseException, InterruptedException, IOException {
        logger.info("Initialising VirageCore.");
        
        this.args = args;
        this.jobs = new LinkedBlockingQueue<VirageJob<?>>();
    }
    
    public ExtendedPrologParser getExtendedPrologParser() {
    	return this.extendedPrologParser;
    }
    
    public VirageSearchManager getSearchManager() {
    	return this.searchManager;
    }
    
    public IsabelleTheoryGenerator getIsabelleTheoryGenerator() {
    	return this.generator;
    }
    
    public FrameworkRepresentation getFrameworkRepresentation() {
    	return this.framework;
    }
    
    public void setFrameworkRepresentation(FrameworkRepresentation framework) {
    	this.framework = framework;
    	this.initAnalyzers();
    }
    
    /**
     * Once started, this method keeps looking for new jobs and executes available ones.
     * <b> Does not return! </b>
     */
    public void run() {
        try {
			this.init(this.args);
		} catch (ParseException e) {
			logger.error("An error occured.", e);
			return;
		}
        
        while(true) {
        	if(!this.jobs.isEmpty()) {
        		logger.debug("VirageJob found.");
        		
        		VirageJob<?> job;
				try {
					job = this.jobs.take();
	        		job.execute(this);
				} catch (InterruptedException e) {
					logger.error("An error occured.", e);
					return;
				}
        	} else {
        		// No jobs, busy waiting
        	}
        }
    }
    
    /**
     * Adds a job to the queue, after ensuring its executability.
     * @param job the job
     */
    public void submit(VirageJob<?> job) {
    	this.jobs.add(job);
    }
    
    private void init(String[] args) throws ParseException {
    	this.parseCommandLine(args);
    	
    	// Initialise UserInterface
    	VirageUserInterfaceFactory factory = new VirageUserInterfaceFactory();
    	if(cl.hasOption("ui")) {
    		String value = cl.getOptionValue("ui");
    		
    		this.ui = factory.getUI(value, this);
    	} else {
    		this.ui = factory.getUI("none", this);
    	}
    	this.ui.launch();
    	
    	this.extendedPrologParser = new SimpleExtendedPrologParser();
    	this.searchManager = new VirageSearchManager();
    }
    
    private void initAnalyzers() {
    	try {
	    	this.searchManager.addAnalyzer(new SimplePrologCompositionAnalyzer(framework));
	    	this.searchManager.addAnalyzer(new AdmissionCheckPrologCompositionAnalyzer(framework));
	    	this.generator = new IsabelleTheoryGenerator(framework.getTheoryPath(), framework);
    	} catch (Exception e) {
    		logger.error("Initialising CompositionAnalyzers failed.", e);
    	}
    }
    
    private void parseCommandLine(String[] args) throws ParseException {
    	Options options = new Options();
    	
    	// This looks terrible, but it is still the recommended way:
    	// https://commons.apache.org/proper/commons-cli/usage.html
    	@SuppressWarnings("all")
    	Option ui = OptionBuilder.withArgName("interface").hasArg().withDescription("the interface to be used (supported: cli)").create("ui");
    	
    	options.addOption(ui);
    	
    	CommandLineParser parser = new DefaultParser();
    	try {
    		this.cl = parser.parse(options, args);
    	} catch (ParseException e){
    		logger.fatal("Something went wrong while parsing the command line parameters.");
    		
    		HelpFormatter formatter = new HelpFormatter();
    		formatter.printHelp("ViRAGe", options);
    		
    		throw e;
    	}
    }
}
