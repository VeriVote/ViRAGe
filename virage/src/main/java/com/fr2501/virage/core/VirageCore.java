package com.fr2501.virage.core;

import java.io.IOException;

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
import com.fr2501.virage.prolog.ExtendedPrologParser;
import com.fr2501.virage.prolog.SimpleExtendedPrologParser;
import com.fr2501.virage.types.FrameworkRepresentation;

/**
 * 
 * The main application
 *
 */

@SuppressWarnings("deprecation")
public class VirageCore {
	private final static Logger logger = LogManager.getLogger(VirageCore.class.getName());
	
	private CommandLine cl;
	
	private VirageUserInterface userInterface = null;
	private ExtendedPrologParser extendedPrologParser = null;
	private VirageSearchManager searchManager = null;
	
	private FrameworkRepresentation framework = null;

    public VirageCore(String[] args) throws ParseException, InterruptedException, IOException {
        logger.info("Initialising VirageCore.");
        
        this.init(args);
        
        while(true) {
        	if(this.userInterface.hasJobs()) {
        		logger.debug("VirageJob found.");
        		VirageJob job = this.userInterface.getJob();
        		
        		if(job.requiresExecutor()) {
        			// Is there a better solution? Wildcards would probably help a bit.
        			if(job instanceof VirageExecutorJob) {
        				if(job instanceof VirageGenerateJob) {
        					((VirageGenerateJob) job).attachExecutor(this.searchManager);
        				} else if(job instanceof VirageAnalyzeJob) {
        					((VirageAnalyzeJob) job).attachExecutor(this.searchManager);
        				} else if(job instanceof VirageParseJob) {
        					((VirageParseJob) job).attachExecutor(this.extendedPrologParser);
        				}
        			}
        		}
        		
        		if(job.requiresFramework()) {
        			if(job instanceof VirageExecutorJobWithFramework) {
        				((VirageExecutorJobWithFramework<?,?>) job).addFramework(this.framework);
        			}
        		}
        		
        		if(job.isReadyToExecute()) {        			
        			job.execute();
        			
        			// Ugly, but required to get a FrameworkRepresentation from anywhere.
        			if(job instanceof VirageParseJob) {
        				if(job.state == VirageJobState.FINISHED) {
        					this.framework = ((VirageParseJob) job).getResult();
        					this.initAnalyzers();
        				}
        			}
        		}
        	} else {
        		// No jobs, busy waiting
        	}
        }
    }
    
    private void init(String[] args) throws ParseException {
    	this.parseCommandLine(args);
    	
    	// Init UserInterface
    	if(cl.hasOption("ui")) {
    		String value = cl.getOptionValue("ui");
    		
    		VirageUserInterfaceFactory factory = new VirageUserInterfaceFactory();
    		this.userInterface = factory.getUI(value);
    	}
    	
    	this.extendedPrologParser = new SimpleExtendedPrologParser();
    	this.searchManager = new VirageSearchManager();
    }
    
    private void initAnalyzers() {
    	try {
	    	this.searchManager.addAnalyzer(new SimplePrologCompositionAnalyzer(framework));
	    	this.searchManager.addAnalyzer(new AdmissionCheckPrologCompositionAnalyzer(framework));
    	} catch (Exception e) {
    		logger.error("Initialising CompositionAnalyzers failed.");
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
