package com.fr2501.virage.core;

import java.io.File;
import java.io.IOException;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

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
import com.fr2501.virage.prolog.MalformedEPLFileException;
import com.fr2501.virage.prolog.SimpleExtendedPrologParser;
import com.fr2501.virage.types.FrameworkRepresentation;
import com.fr2501.virage.types.Property;

/**
 * 
 * The main application
 *
 */

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
        		
        		switch(job.getType()) {
        		case PARSE_EPL: 
        			if(this.extendedPrologParser == null) {
        				this.extendedPrologParser = new SimpleExtendedPrologParser();
        			}
        			
        			String path = job.getArguments().get(0);
        			try {
        				this.framework = this.extendedPrologParser.parseFramework(new File(path));
        			} catch(Exception e) {
        				logger.error("Something went wrong while reading the file.");
        			}
        			
        			break;
        		case GENERATE:
        			if(this.searchManager == null) {
        				this.searchManager = new VirageSearchManager();
        				this.searchManager.addAnalyzer(new SimplePrologCompositionAnalyzer(this.framework));
        				this.searchManager.addAnalyzer(new AdmissionCheckPrologCompositionAnalyzer(this.framework));
        			}
        			
        			String propertyString = job.getArguments().get(0);
        			String[] properties = propertyString.split(",");
        			Set<Property> propertySet = new HashSet<Property>();
        			for(String property: properties) {
        				propertySet.add(this.framework.getProperty(property));
        			}
        			
        			try {
        				this.searchManager.generateComposition(propertySet);
        			} catch(Exception e) {
        				logger.error("Something went wrong while generating the composition.");
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
