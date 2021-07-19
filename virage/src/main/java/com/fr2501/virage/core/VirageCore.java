package com.fr2501.virage.core;

import com.fr2501.virage.analyzer.AdmissionCheckPrologCompositionAnalyzer;
import com.fr2501.virage.beast.CCodeGenerator;
import com.fr2501.virage.isabelle.IsabelleCodeGenerator;
import com.fr2501.virage.isabelle.IsabelleProofChecker;
import com.fr2501.virage.isabelle.IsabelleTheoryGenerator;
import com.fr2501.virage.jobs.VirageExitJob;
import com.fr2501.virage.jobs.VirageJob;
import com.fr2501.virage.jobs.VirageJobState;
import com.fr2501.virage.prolog.ExtendedPrologParser;
import com.fr2501.virage.prolog.SimpleExtendedPrologParser;
import com.fr2501.virage.types.ExternalSoftwareUnavailableException;
import com.fr2501.virage.types.FrameworkRepresentation;
import com.fr2501.virage.types.IsabelleBuildFailedException;

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
import org.jpl7.JPLException;

/**
 * The main application.
 *
 */

// This is required due to Commons CLI still recommending the deprecated way of building Options.
@SuppressWarnings("deprecation")
public class VirageCore implements Runnable {
    private static final Logger logger = LogManager.getLogger(VirageCore.class.getName());

    private static final String _VERSION = "0.1.0";

    private CommandLine cl;
    private String[] args;
    private VirageUserInterface ui;

    private ExtendedPrologParser extendedPrologParser;
    private VirageSearchManager searchManager;
    private IsabelleTheoryGenerator theoryGenerator;
    private IsabelleProofChecker checker;
    private IsabelleCodeGenerator scalaCodeGenerator;
    private CCodeGenerator cCodeGenerator;
    private FrameworkRepresentation framework;

    private BlockingQueue<VirageJob<?>> jobs;

    /**
     * Initialises VirageCore with the given arguments.
     * 
     * @param args the arguments
     */
    public VirageCore(String[] args) {
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
        return this.theoryGenerator;
    }

    public IsabelleProofChecker getIsabelleProofChecker() {
        return this.checker;
    }

    public IsabelleCodeGenerator getIsabelleCodeGenerator() {
        return this.scalaCodeGenerator;
    }

    public FrameworkRepresentation getFrameworkRepresentation() {
        return this.framework;
    }

    /**
     * Sets the core's {@link FrameworkRepresentation} and reinitializes its analyzers.
     * 
     * @param framework the new {@link FrameworkRepresentation}
     */
    public void setFrameworkRepresentation(FrameworkRepresentation framework) {
        this.framework = framework;

        this.initAnalyzers();
    }

    /**
     * Destroys the VirageCore and terminates ViRAGe.
     * 
     * @param statusCode ViRAGe's exit code
     */
    public void destroy(int statusCode) {
        if (this.checker != null) {
            this.checker.destroy();
        }

        System.exit(statusCode);
    }

    /**
     * Once started, this method keeps looking for new jobs and executes available ones. <b> Does
     * not return! </b>
     */
    public void run() {
        try {
            this.init(this.args);
        } catch (ParseException e) {
            logger.error("An error occured.", e);
            return;
        }

        while (true) {
            if (!this.jobs.isEmpty()) {
                logger.debug("VirageJob found.");

                VirageJob<?> job;
                try {
                    job = this.jobs.take();

                    this.ui.displayMessage("---------- " + job.getDescription());

                    job.execute(this);
                } catch (Exception e) {
                    logger.error("An error occured.", e);
                }
            } else {
                // No jobs, busy waiting
                try {
                    Thread.sleep(100);
                } catch (InterruptedException e) {
                    // TODO Auto-generated catch block
                    e.printStackTrace();
                }
            }
        }
    }

    /**
     * Adds a job to the queue, after ensuring its executability.
     * 
     * @param job the job
     */
    public void submit(VirageJob<?> job) {
        if (!job.externalSoftwareAvailable()) {
            job.setState(VirageJobState.FAILED);

            logger.warn("External software unavailable!");

            return;
        }
        
        if(job instanceof VirageExitJob) {
            job.execute(this);
        }

        this.jobs.add(job);
    }

    private void init(String[] args) throws ParseException {
        this.parseCommandLine(args);

        // Initialise UserInterface
        VirageUserInterfaceFactory factory = new VirageUserInterfaceFactory();
        if (cl.hasOption("ui")) {
            String value = cl.getOptionValue("ui");

            this.ui = factory.getUi(value, this);
        } else {
            this.ui = factory.getUi("none", this);
        }
        this.ui.launch();

        this.extendedPrologParser = new SimpleExtendedPrologParser();
        this.searchManager = new VirageSearchManager();
    }

    private void initAnalyzers() {
        boolean unsafeState = false;

        try {
            // this.searchManager.addAnalyzer(new
            // SimplePrologCompositionAnalyzer(framework));
            this.searchManager.addAnalyzer(new AdmissionCheckPrologCompositionAnalyzer(framework));
            // this.searchManager.addAnalyzer(new SBMCCompositionAnalyzer(framework));
            this.theoryGenerator = new IsabelleTheoryGenerator(framework.getTheoryPath(),
                    framework);
            this.cCodeGenerator = new CCodeGenerator(this.framework);
        } catch (IOException e) {
            logger.error(e);

            unsafeState = true;
        } catch (UnsatisfiedLinkError e) {
            this.ui.displayError("SWI-Prolog library directory could not be located.");

            String newValue;
            try {
                newValue = this.ui.requestString(
                        "Please input the path to the SWI-Prolog " + "library directory.\n"
                                + "For your setup of SWI-Prolog, the typical value is \""
                                + ConfigReader.getInstance().getSwiplLib()
                                + "\", but this might differ on your system.");

                if (!newValue.isEmpty()) {
                    ConfigReader.getInstance().updateValueForLdLibraryPath(newValue);
                }
            } catch (ExternalSoftwareUnavailableException e1) {
                // TODO Auto-generated catch block
                e1.printStackTrace();
            }

            unsafeState = true;
        } catch (ExternalSoftwareUnavailableException e) {
            this.ui.displayError("libswipl.so could not be located.");

            String newValue;
            try {
                newValue = this.ui.requestString("Please input the path to libswipl.so.\n"
                        + "For your setup of SWI-Prolog, typical values are \"/usr/lib/libswipl.so\" or \""
                        + ConfigReader.getInstance().getSwiplLib() + "libswipl.so\""
                        + ", but this might differ on your system.");

                if (!newValue.isEmpty()) {
                    ConfigReader.getInstance().updateValueForLdPreload(newValue);
                }
            } catch (ExternalSoftwareUnavailableException e1) {
                // TODO Auto-generated catch block
                e1.printStackTrace();
            }

            unsafeState = true;
        } catch (JPLException e) {
            logger.error("SWI-Prolog appears to be outdated. Please refer to ViRAGe's readme.", e);
            unsafeState = true;
        }

        if (unsafeState) {
            this.ui.displayMessage("A restart is required for the changes to take effect.\n"
                    + "Please restart ViRAGe after it terminated.");
            System.exit(0);
        }

        if (ConfigReader.getInstance().hasIsabelle()) {
            try {
                this.checker = IsabelleProofChecker.getInstance(framework.getSessionName(),
                        framework.getTheoryPath());
                this.checker.setSolvers(ConfigReader.getInstance().getIsabelleTactics());

                this.scalaCodeGenerator = new IsabelleCodeGenerator(this.framework);
            } catch (IOException e) {
                // TODO Auto-generated catch block
                e.printStackTrace();
            } catch (ExternalSoftwareUnavailableException e) {
                // TODO
                e.printStackTrace();
            } catch (IsabelleBuildFailedException e) {
                // TODO Auto-generated catch block
                e.printStackTrace();
            }
        }
    }

    private void parseCommandLine(String[] args) throws ParseException {
        Options options = new Options();

        // This looks terrible, but it is still the recommended way:
        // https://commons.apache.org/proper/commons-cli/usage.html
        @SuppressWarnings("all")
        Option ui = OptionBuilder.withArgName("interface").hasArg()
                .withDescription("the interface to be used (supported: cli)").create("ui");

        options.addOption(ui);

        CommandLineParser parser = new DefaultParser();
        try {
            this.cl = parser.parse(options, args);
        } catch (ParseException e) {
            logger.fatal("Something went wrong while parsing the command line parameters.");

            HelpFormatter formatter = new HelpFormatter();
            formatter.printHelp("ViRAGe", options);

            throw e;
        }
    }

    public static String getVersion() {
        return _VERSION;
    }
    
    public CCodeGenerator getCCodeGenerator() {
        return this.cCodeGenerator;
    }
}
