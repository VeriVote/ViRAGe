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
import org.jpl7.JPLException;

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

/**
 * The main application.
 *
 * @author VeriVote
 */

// This is required due to Commons CLI still recommending the deprecated way of building Options.
@SuppressWarnings("deprecation")
public final class VirageCore implements Runnable {
    /**
     * The logger.
     */
    private static final Logger LOGGER = LogManager.getLogger(VirageCore.class.getName());

    /**
     * ViRAGe versiom.
     */
    private static final String VERSION = "0.1.0";

    /**
     * Command line argument container.
     */
    private CommandLine cl;
    /**
     * Command line arguments.
     */
    private final String[] args;

    /**
     * The user interface.
     */
    private VirageUserInterface ui;

    /**
     * The (E)PL parser.
     */
    private ExtendedPrologParser extendedPrologParser;
    /**
     * The search manager.
     */
    private VirageSearchManager searchManager;
    /**
     * The Isabelle theory generator.
     */
    private IsabelleTheoryGenerator theoryGenerator;
    /**
     * The Isabelle proof checker.
     */
    private IsabelleProofChecker checker;
    /**
     * The Isabelle Scala generator.
     */
    private IsabelleCodeGenerator scalaCodeGenerator;
    /**
     * The C code generator.
     */
    private CCodeGenerator cCodeGenerator;
    /**
     * The Compositional Framework.
     */
    private FrameworkRepresentation framework;

    /**
     * The ViRAGeJob queue.
     */
    private final BlockingQueue<VirageJob<?>> jobs;

    /**
     * Initialises VirageCore with the given arguments.
     *
     * @param args the arguments
     */
    public VirageCore(final String[] args) {
        LOGGER.info("Initialising VirageCore.");

        this.args = args;
        this.jobs = new LinkedBlockingQueue<VirageJob<?>>();
    }

    public static String getVersion() {
        return VERSION;
    }

    /**
     * Destroys the VirageCore and terminates ViRAGe.
     *
     * @param statusCode ViRAGe's exit code
     */
    public void destroy(final int statusCode) {
        if (this.checker != null) {
            this.checker.destroy();
        }

        System.exit(statusCode);
    }

    public CCodeGenerator getCCodeGenerator() {
        return this.cCodeGenerator;
    }

    public ExtendedPrologParser getExtendedPrologParser() {
        return this.extendedPrologParser;
    }

    public FrameworkRepresentation getFrameworkRepresentation() {
        return this.framework;
    }

    public IsabelleCodeGenerator getIsabelleCodeGenerator() {
        return this.scalaCodeGenerator;
    }

    public IsabelleProofChecker getIsabelleProofChecker() {
        return this.checker;
    }

    public IsabelleTheoryGenerator getIsabelleTheoryGenerator() {
        return this.theoryGenerator;
    }

    public VirageSearchManager getSearchManager() {
        return this.searchManager;
    }

    private void init(final String[] args) throws ParseException {
        this.parseCommandLine(args);

        // Initialise UserInterface
        final VirageUserInterfaceFactory factory = new VirageUserInterfaceFactory();
        if (this.cl.hasOption("ui")) {
            final String value = this.cl.getOptionValue("ui");

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
            this.searchManager
            .addAnalyzer(new AdmissionCheckPrologCompositionAnalyzer(this.framework));
            // this.searchManager.addAnalyzer(new SBMCCompositionAnalyzer(framework));
            this.theoryGenerator = new IsabelleTheoryGenerator(this.framework.getTheoryPath(),
                    this.framework);
            this.cCodeGenerator = new CCodeGenerator(this.framework);
        } catch (final IOException e) {
            LOGGER.error(e);

            unsafeState = true;
        } catch (final UnsatisfiedLinkError e) {
            this.ui.displayError("SWI-Prolog library directory could not be located.");

            final String newValue;
            try {
                newValue = this.ui.requestString(
                        "Please input the path to the SWI-Prolog " + "library directory.\n"
                                + "For your setup of SWI-Prolog, the typical value is \""
                                + ConfigReader.getInstance().getSwiplLib()
                                + "\", but this might differ on your system.");

                if (!newValue.isEmpty()) {
                    ConfigReader.getInstance().updateValueForSwiPrologLibrariesPath(newValue);
                }
            } catch (final ExternalSoftwareUnavailableException e1) {
                // TODO Auto-generated catch block
                e1.printStackTrace();
            }

            unsafeState = true;
        } catch (final ExternalSoftwareUnavailableException e) {
            this.ui.displayError("libswipl.so could not be located.");

            final String newValue;
            try {
                newValue = this.ui.requestString("Please input the path to libswipl.so.\n"
                        + "For your setup of SWI-Prolog, "
                        + "typical values are \"/usr/lib/libswipl.so\" or \""
                        + ConfigReader.getInstance().getSwiplLib() + "libswipl.so\""
                        + ", but this might differ on your system.");

                if (!newValue.isEmpty()) {
                    ConfigReader.getInstance().updateValueForLibswiplPath(newValue);
                }
            } catch (final ExternalSoftwareUnavailableException e1) {
                // TODO Auto-generated catch block
                e1.printStackTrace();
            }

            unsafeState = true;
        } catch (final JPLException e) {
            LOGGER.error("SWI-Prolog appears to be outdated. Please refer to ViRAGe's readme.", e);
            unsafeState = true;
        }

        if (unsafeState) {
            this.ui.displayMessage("A restart is required for the changes to take effect.\n"
                    + "Please restart ViRAGe after it terminated.");
            System.exit(0);
        }

        if (ConfigReader.getInstance().hasIsabelle()) {
            try {
                this.checker = IsabelleProofChecker.getInstance(this.framework.getSessionName(),
                        this.framework.getTheoryPath());
                this.checker.setSolvers(ConfigReader.getInstance().getIsabelleTactics());

                this.scalaCodeGenerator = new IsabelleCodeGenerator(this.framework);
            } catch (final IOException e) {
                // TODO Auto-generated catch block
                e.printStackTrace();
            } catch (final ExternalSoftwareUnavailableException e) {
                // TODO
                e.printStackTrace();
            } catch (final IsabelleBuildFailedException e) {
                // TODO Auto-generated catch block
                e.printStackTrace();
            }
        }
    }

    private void parseCommandLine(final String[] args) throws ParseException {
        final Options options = new Options();

        OptionBuilder.withArgName("interface");
        OptionBuilder.hasArg();
        OptionBuilder.withDescription("the interface to be used (supported: cli)");
        // This looks terrible, but it is still the recommended way:
        // https://commons.apache.org/proper/commons-cli/usage.html
        @SuppressWarnings("all")
        final Option ui = OptionBuilder.create("ui");

        options.addOption(ui);

        final CommandLineParser parser = new DefaultParser();
        try {
            this.cl = parser.parse(options, args);
        } catch (final ParseException e) {
            LOGGER.fatal("Something went wrong while parsing the command line parameters.");

            final HelpFormatter formatter = new HelpFormatter();
            formatter.printHelp("ViRAGe", options);

            throw e;
        }
    }

    /**
     * Once started, this method keeps looking for new jobs and executes available ones. <b> Does
     * not return! </b>
     */
    @Override
    public void run() {
        try {
            this.init(this.args);
        } catch (final ParseException e) {
            LOGGER.error("An error occured.", e);
            return;
        }

        while (true) {
            if (!this.jobs.isEmpty()) {
                LOGGER.debug("VirageJob found.");

                final VirageJob<?> job;
                try {
                    job = this.jobs.take();

                    this.ui.displayMessage("---------- " + job.getDescription());

                    job.execute(this);
                    // Checkstyle does not like this catch-all block.
                    // I think it's justified here, as this is the last
                    // reasonable point to catch exceptions without
                    // escalating to the main function and crashing the
                    // program. The type of exceptions is unknown, as
                    // job.execute can do virtually anything.
                } catch (final Exception e) {
                    LOGGER.error("An error occured.", e);
                }
            } else {
                // No jobs, busy waiting
                try {
                    Thread.sleep(100);
                } catch (final InterruptedException e) {
                    // TODO Auto-generated catch block
                    e.printStackTrace();
                }
            }
        }
    }

    /**
     * Sets the core's {@link FrameworkRepresentation} and reinitializes its analyzers.
     *
     * @param framework the new {@link FrameworkRepresentation}
     */
    public void setFrameworkRepresentation(final FrameworkRepresentation framework) {
        this.framework = framework;

        this.initAnalyzers();
    }

    /**
     * Adds a job to the queue, after ensuring its executability.
     *
     * @param job the job
     */
    public void submit(final VirageJob<?> job) {
        if (!job.externalSoftwareAvailable()) {
            job.setState(VirageJobState.FAILED);

            LOGGER.warn("External software unavailable!");

            return;
        }

        if (job instanceof VirageExitJob) {
            job.execute(this);
        }

        this.jobs.add(job);
    }
}
