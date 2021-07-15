package com.fr2501.virage.core;

import com.fr2501.util.StringUtils;
import com.fr2501.virage.jobs.VirageAnalyzeJob;
import com.fr2501.virage.jobs.VirageDummyJob;
import com.fr2501.virage.jobs.VirageExitJob;
import com.fr2501.virage.jobs.VirageExtractJob;
import com.fr2501.virage.jobs.VirageGenerateJob;
import com.fr2501.virage.jobs.VirageIsabelleGenerateJob;
import com.fr2501.virage.jobs.VirageIsabelleGenerateScalaJob;
import com.fr2501.virage.jobs.VirageIsabelleVerifyJob;
import com.fr2501.virage.jobs.VirageJob;
import com.fr2501.virage.jobs.VirageJobState;
import com.fr2501.virage.jobs.VirageParseJob;
import com.fr2501.virage.jobs.VirageProveJob;
import com.fr2501.virage.prolog.JplFacade;
import com.fr2501.virage.types.Component;
import com.fr2501.virage.types.ComposableModule;
import com.fr2501.virage.types.CompositionProof;
import com.fr2501.virage.types.CompositionalStructure;
import com.fr2501.virage.types.DecompositionTree;
import com.fr2501.virage.types.ExternalSoftwareUnavailableException;
import com.fr2501.virage.types.FrameworkRepresentation;
import com.fr2501.virage.types.InvalidConfigVersionException;
import com.fr2501.virage.types.Property;
import java.io.File;
import java.io.BufferedWriter;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStreamWriter;
import java.io.StringWriter;
import java.io.Writer;
import java.nio.charset.StandardCharsets;
import java.time.LocalDateTime;
import java.time.format.DateTimeFormatter;
import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedList;
import java.util.List;
import java.util.Scanner;

import org.apache.commons.io.IOUtils;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

/**
 * A simple command line interface for ViRAGe.
 *
 */
public class VirageCommandLineInterface implements VirageUserInterface {
    private final Logger logger = LogManager.getLogger(VirageCommandLineInterface.class);
    private Scanner scanner;
    private VirageCore core;

    private CommandLineProgressIndicator clpi;
    
    private Writer outputWriter;

    private static final String SEPARATOR = "###########################################################";
    private static final String BANNER = "#\n"
            + "# Y88b      / ,e, 888~-_        e       e88~~\\           \n"
            + "#  Y88b    /   \"  888   \\      d8b     d888      e88~~8e \n"
            + "#   Y88b  /   888 888    |    /Y88b    8888 __  d888  88b\n"
            + "#    Y888/    888 888   /    /  Y88b   8888   | 8888__888\n"
            + "#     Y8/     888 888_-~    /____Y88b  Y888   | Y888    ,\n"
            + "#      Y      888 888 ~-_  /      Y88b  \"88__/   \"88___/ \n#";

    private Thread thread;

    protected VirageCommandLineInterface(VirageCore core) {
        this.outputWriter = new BufferedWriter(new OutputStreamWriter(System.out), 256);

        logger.info("Initialising VirageCommandLineInterface.");

        this.scanner = new Scanner(System.in);
        this.core = core;

        this.printSeparator(); /* ----- */

        this.printBanner();

        this.printSeparator(); /* ----- */

        this.checkSettingsCompatibility();
        this.printTimestamp();

        this.printSeparator(); /* ----- */

        this.printPurpose();

        this.printSeparator(); /* ----- */

        this.checkEnvironment();

        this.printSeparator(); /* ----- */

        this.printSettings();

        this.printSeparator(); /* ----- */

        this.clpi = new CommandLineProgressIndicator();
    }

    private void printSeparator() {
        this.displayMessage(SEPARATOR);
    }

    private void printBanner() {
        this.displayMessage(BANNER);
    }

    private void checkSettingsCompatibility() {
        try {
            ConfigReader.getInstance().readConfigFile(false);
        } catch (InvalidConfigVersionException e) {
            this.displayMessage("# " + e.getMessage());
            if (this.requestConfirmation(
                    "# ViRAGe can replace the settings file with an up-to-date one. "
                            + "Your old settings file will be moved to \"old_settings\", and as many settings "
                            + "as possible will be transferred. "
                            + "Do you want to let ViRAGe perform this operation?")) {
                try {
                    try {
                        ConfigReader.getInstance().readConfigFile(true);
                    } catch (InvalidConfigVersionException e1) {
                        // NO-OP, this cannot happen.
                        // readConfigFile(true) overwrites the old config.
                    }
                } catch (IOException e1) {
                    // TODO Auto-generated catch block
                    e1.printStackTrace();
                }
            } else {
                this.displayMessage("# ViRAGe is in an unsafe state as you "
                        + "loaded an outdated configuration.");

                if (!this.requestConfirmation("Do you want to continue anyways?")) {
                    this.core.submit(new VirageExitJob(this, 0));
                }
            }

        } catch (IOException e) {
            // TODO
            e.printStackTrace();
        }
    }

    private void printTimestamp() {
        DateTimeFormatter dtf = DateTimeFormatter.ofPattern("yyyy-MM-dd HH:mm:ss");
        LocalDateTime now = LocalDateTime.now();
        this.displayMessage(
                "# Version " + VirageCore.getVersion() + ", Timestamp: " + dtf.format(now));
        this.displayMessage("# If you need help, type \"help\", \"h\" or \"?\".");
        this.displayMessage("# To exit ViRAGe, type \"exit\".");
    }

    private void printPurpose() {
        this.displayMessage("# ViRAGe is a tool to generate voting rules and automatically ");
        this.displayMessage("# reason about their social choice properties.");
    }

    private void checkEnvironment() {
        this.displayMessage("# " + ConfigReader.getInstance().checkAvailabilityAndGetVersions()
                .replace("\n", "\n# "));

        boolean unsafeState = false;
        try {
            JplFacade facade = new JplFacade();
        } catch (ExternalSoftwareUnavailableException e) {
            this.displayError(
                    "A required SWI-Prolog library (\"libswipl.so\") could not be located.");

            String newValue;
            try {
                while (true) {
                    newValue = this.requestString("Please input the path to libswipl.so. "
                            + "For your setup of SWI-Prolog, typical values are "
                            + "\"/usr/lib/libswipl.so\" or \""
                            + ConfigReader.getInstance().getSwiplLib() + "libswipl.so\""
                            + ", but this might differ on your system.");

                    if (!newValue.isEmpty()) {
                        final File file = new File(newValue);
                        if (!file.exists()) {
                            this.displayError("This file does not exist. Please try again.");
                            continue;
                        }

                        if (!newValue.endsWith("libswipl.so")) {
                            this.displayError("This is not \"libswipl.so\". Please try again.");
                            continue;
                        }

                        ConfigReader.getInstance().updateValueForLdPreload(newValue);
                        break;
                    }
                }
            } catch (ExternalSoftwareUnavailableException e1) {
                // TODO Auto-generated catch block
                e1.printStackTrace();
            }

            unsafeState = true;
        } catch (UnsatisfiedLinkError e) {
            this.displayError("The SWI-Prolog library directory could not be located. "
                    + "This directory must contain the library \"libjpl.so\", otherwise "
                    + "ViRAGe will not work properly.");

            String newValue;
            try {
                while (true) {
                    newValue = this.requestString(
                            "Please input the path to the SWI-Prolog " + "library directory. "
                                    + "For your setup of SWI-Prolog, the typical value is \""
                                    + ConfigReader.getInstance().getSwiplLib()
                                    + "\", but this might differ on your system.");

                    if (!newValue.isEmpty()) {
                        File file = new File(newValue);
                        if (!file.exists()) {
                            this.displayError("This directory does not exist. Please try again.");
                            continue;
                        } else if (!file.isDirectory()) {
                            this.displayError("This path is not a directory. Please try again.");
                            continue;
                        } else if (!(new File(newValue + File.separator + "libjpl.so").exists())) {
                            this.displayError("This directory does not contain \"libjpl.so\". "
                                    + "You either supplied the wrong directory, "
                                    + "or JPL is not installed.");
                            continue;
                        }

                        ConfigReader.getInstance().updateValueForLdLibraryPath(newValue);
                        break;
                    }
                }
            } catch (ExternalSoftwareUnavailableException e1) {
                // TODO Auto-generated catch block
                e1.printStackTrace();
            }

            unsafeState = true;
        }

        if (unsafeState) {
            this.displayMessage("A restart is required for the changes to take effect. "
                    + "Please restart ViRAGe after it terminated.");
            System.exit(0);
        }
    }

    private void printSettings() {
        this.displayMessage("# Reading configuration from " + ConfigReader.getConfigPath() + ".");
        this.displayMessage("#");
        this.displayMessage("# The following settings were found: ");

        List<String> propertyNames = new LinkedList<String>();
        for (String s : ConfigReader.getInstance().getAllProperties().keySet()) {
            propertyNames.add(s);
        }
        Collections.sort(propertyNames);

        String lastPrefix = "";
        for (String s : propertyNames) {
            if (!lastPrefix.equals(s.split("_")[0])) {
                this.displayMessage("#");
                lastPrefix = s.split("_")[0];
            }

            String value = ConfigReader.getInstance().getAllProperties().get(s).replaceAll(";",
                    ";\n#\t");

            if (value.isEmpty()) {
                value = "NOT_SET";
            }

            this.displayMessage("# " + s.toUpperCase() + ":\n#\t" + value);
        }

        if (this.requestConfirmation(
                "# Do you want to edit these settings? " + "This will open the configuration "
                        + "file in a text editor and require a restart of ViRAGe.")) {

            try {
                this.displayMessage("# If ViRAGe freezes without opening an editor, "
                        + "please try another one by setting \"SYSTEM_TEXT_EDITOR\" in "
                        + ConfigReader.getConfigPath() + ". At the moment, only windowed "
                        + "editors (mousepad, ...) are supported, not in-terminal ones "
                        + "(nano, vim, ...).");

                ConfigReader.getInstance().openConfigFileForEditing();

                this.displayMessage("# Please restart ViRAGe for the changes to take effect.");

                System.exit(0);
            } catch (ExternalSoftwareUnavailableException e) {
                this.displayMessage(
                        "# No text editor available. Please set the configuration option "
                                + "\"SYSTEM_TEXT_EDITOR\" or the environment variable \"EDITOR\".");
            }
        }
    }

    /**
     * Similar to run(), but creates its own new thread.
     */
    public void launch() {
        this.thread = new Thread(this, "vcli");
        this.thread.start();
    }

    @Override
    public void run() {
        logger.info("Started VirageCommandLineInterface.");

        String defaultPath = "./src/test/resources/framework.pl";

        String path;

        boolean firstTry = true;

        while (true) {
            if (ConfigReader.getInstance().hasPathToRootFile() && firstTry && this
                    .requestConfirmation("Configuration option \"ISABELLE_PATH_TO_ROOT_FILE\" "
                            + "is specified as \"" + ConfigReader.getInstance().getPathToRootFile()
                            + "\". "
                            + "Do you want to use this Isabelle ROOT file to generate an (E)PL file?")) {
                path = ConfigReader.getInstance().getPathToRootFile();

                firstTry = false;
            } else {
                path = this.requestString("Please input the path to an (E)PL file or "
                        + "an Isabelle ROOT file containing exactly one session specification. "
                        + "(Press ENTER for default: " + defaultPath + ")");
            }

            if (path.equals("")) {
                path = defaultPath;
            }

            if (this.extractAndOrParseFramework(path) != null) {
                break;
            }
        }

        while (true) {
            String arg = this
                    .requestString("Do you want to (g)enerate a composition, (a)nalyze one, "
                            + "(p)rove a claim,\n"
                            + "generate (I)sabelle proofs or generate (S)cala code?");

            VirageJob<?> job = null;

            // TODO Refactor to enum
            if (arg.equals("g")) {
                job = this.createGenerationQuery();
            } else if (arg.equals("a")) {
                job = this.createAnalysisQuery();
            } else if (arg.equals("p")) {
                job = this.createProofQuery();
            } else if (arg.equals("I")) {
                job = this.createIsabelleQuery();
            } else if (arg.equals("S")) {
                job = this.createCodeGenerationQuery();
            } else {
                this.displayMessage("Please try again.");
                continue;
            }

            this.core.submit(job);
            // VirageCore is intended to work on jobs asynchronously
            // and that is perfectly possible. It just does not make
            // too much sense when using a CLI, so it is disabled.
            job.waitFor();
        }
    }

    private FrameworkRepresentation extractAndOrParseFramework(String path) {
        FrameworkRepresentation framework = null;
        VirageParseJob parseJob;

        if (!path.endsWith(".pl")) {
            if (path.endsWith("ROOT")) {
                path = path.substring(0, path.length() - "ROOT".length());
            }

            File file = new File(path);
            if (file.isDirectory()) {
                File[] files = file.listFiles();

                List<File> plFiles = new LinkedList<File>();
                for (File child : files) {
                    if (child.getAbsolutePath().endsWith(".pl")) {
                        plFiles.add(child);
                    }
                }

                if (!plFiles.isEmpty()) {
                    int idx = this.chooseAlternative("The following (E)PL files were found. "
                            + "Do you want to use one of those and skip (E)PL generation? "
                            + "This saves time if no changes to the Isabelle theories were "
                            + "made since the (E)PL file was created.", plFiles);

                    if (idx != -1) {
                        return this.extractAndOrParseFramework(plFiles.get(idx).getAbsolutePath());
                    }
                }
            }

            if (!ConfigReader.getInstance().hasIsabelle()) {
                this.displayMessage("Isabelle is not available. "
                        + "Please install Isabelle or supply an (E)PL-file directly.");

                return null;
            }

            String sessionName;
            if (ConfigReader.getInstance().hasSessionName() && this.requestConfirmation(
                    "Configuration option " + "\"ISABELLE_SESSION_NAME\" is specified " + "as \""
                            + ConfigReader.getInstance().getSessionName()
                            + "\". Is this the name of the session specified within the given ROOT file?")) {

                sessionName = ConfigReader.getInstance().getSessionName();

                this.displayMessage("Extracting (E)PL file from session \"" + sessionName + "\" at "
                        + path + ".\n" + "This might take some time.");
            } else {
                sessionName = this.requestString(
                        "Please input the name of " + "the session within this directory.");
            }

            VirageExtractJob extractJob = new VirageExtractJob(this, path, sessionName);
            this.core.submit(extractJob);
            extractJob.waitFor();
            if (extractJob.getState().equals(VirageJobState.FAILED)) {
                return null;
            }
            framework = extractJob.getResult();

            parseJob = new VirageParseJob(this, new File(framework.getAbsolutePath()));
        } else {
            parseJob = new VirageParseJob(this, new File(path));
        }

        this.displayMessage("The following operation might take some time, "
                + "especially when ViRAGe is run with previously " + "un-built Isabelle sessions.");
        this.core.submit(parseJob);
        parseJob.waitFor();

        // Unelegant, but prevents race condition where user prompt is printed
        // before the result.
        try {
            Thread.sleep(100);
        } catch (InterruptedException e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
        }

        if (!parseJob.getState().equals(VirageJobState.FINISHED)) {
            return null;
        }

        return parseJob.getResult();
    }

    @Override
    public void notify(VirageJob<?> job) {
        this.displayMessage(job.presentResult() + "\n");
    }

    private VirageGenerateJob createGenerationQuery() {
        String propertyString = this.requestPropertyString();

        List<String> properties = StringUtils.separate(",", propertyString);

        VirageGenerateJob res = new VirageGenerateJob(this, properties);
        return res;
    }

    private VirageAnalyzeJob createAnalysisQuery() {
        String composition = this.requestCompositionString();

        String propertyString = this.requestPropertyString();

        List<String> properties = StringUtils.separate(",", propertyString);

        VirageAnalyzeJob res = new VirageAnalyzeJob(this, composition, properties);
        return res;
    }

    private VirageProveJob createProofQuery() {
        String composition = this.requestCompositionString();

        String propertyString = this.requestPropertyString();

        return this.createProofQuery(composition, propertyString);
    }

    private VirageProveJob createProofQuery(String composition, String propertyString) {
        List<String> properties = StringUtils.separate(",", propertyString);

        VirageProveJob res = new VirageProveJob(this, composition, properties);
        return res;
    }

    private VirageJob<?> createIsabelleQuery() {
        final String composition = this.requestCompositionString();

        final String propertyString = this.requestPropertyString();

        String defaultPath = ConfigReader.getInstance().getDefaultOutputPath();
        String outputPath = this.requestString("Please specify a directory for the "
                + "generated theory file. (Press ENTER for default: " + defaultPath + ")");
        if (outputPath.isEmpty()) {
            outputPath = defaultPath;
        }

        boolean verify = true;
        while (true) {
            if (this.requestConfirmation(
                    "Shall the resulting theory file be verified automatically?")) {
                break;
            } else {
                verify = false;
                break;
            }
        }

        VirageProveJob proveJob = this.createProofQuery(composition, propertyString);
        this.core.submit(proveJob);
        proveJob.waitFor();

        if (proveJob.getState() == VirageJobState.FAILED) {
            logger.warn("Proving the given claims failed.");
            return new VirageDummyJob(this);
        }

        List<List<CompositionProof>> proofLists = proveJob.getResult();
        List<CompositionProof> bestProof = new LinkedList<CompositionProof>();
        for (List<CompositionProof> proof : proofLists) {
            if (proof.size() > bestProof.size()) {
                bestProof = proof;
            }
        }

        VirageIsabelleGenerateJob generateJob = new VirageIsabelleGenerateJob(this, composition,
                bestProof, outputPath);
        if (!verify) {
            return generateJob;
        }
        this.core.submit(generateJob);
        generateJob.waitFor();

        VirageIsabelleVerifyJob verifyJob = new VirageIsabelleVerifyJob(this,
                generateJob.getResult());
        return verifyJob;
    }

    private VirageIsabelleGenerateScalaJob createCodeGenerationQuery() {
        String composition = this.requestCompositionString();

        VirageIsabelleGenerateScalaJob res = new VirageIsabelleGenerateScalaJob(this, composition);
        return res;
    }

    // TODO Change to return List<Property> maybe?
    private String requestPropertyString() {
        FrameworkRepresentation framework = this.core.getFrameworkRepresentation();

        String propertiesString = this.requestString("Please input the desired "
                + "properties (separated by ',') or leave empty to display available properties.");

        propertiesString = StringUtils.removeWhitespace(propertiesString);

        boolean invalid = false;

        if (!propertiesString.isEmpty()) {
            String[] propertyStrings = propertiesString.split(",");
            for (String propertyString : propertyStrings) {
                Property property = framework.getProperty(propertyString);

                if (property == null) {
                    logger.error("Property \"" + propertyString + "\" is undefined.");

                    invalid = true;
                    break;
                }
            }
        }

        if (propertiesString.isEmpty() || invalid) {
            List<String> sortedProps = new ArrayList<String>();
            for (Property p : this.core.getFrameworkRepresentation().getProperties()) {
                if (p.getArity() == 1) {
                    sortedProps.add("\t" + p.getName());
                }
            }
            Collections.sort(sortedProps);

            for (String s : sortedProps) {
                this.displayMessage(s);
            }

            return this.requestPropertyString();
        }

        return propertiesString;
    }

    private String requestCompositionString() {
        boolean invalid = false;

        String compositionString = this
                .requestString("Please input a composition (in Prolog format) "
                        + "or leave empty to display available components.");

        compositionString = StringUtils.removeWhitespace(compositionString);

        if (!compositionString.isEmpty()) {
            try {
                DecompositionTree.parseString(compositionString);
            } catch (Exception e) {
                logger.error("\"" + compositionString
                        + "\" could not be parsed. Please check the brackets and try again.");
                invalid = true;
            }
        }

        if (compositionString.isEmpty() || invalid) {
            List<String> sortedStrings = new ArrayList<String>();
            for (Component c : this.core.getFrameworkRepresentation().getComponents()) {
                sortedStrings.add("\t" + c.toString());
            }
            for (ComposableModule c : this.core.getFrameworkRepresentation()
                    .getComposableModules()) {
                sortedStrings.add("\t" + c.toString());
            }
            for (CompositionalStructure c : this.core.getFrameworkRepresentation()
                    .getCompositionalStructures()) {
                sortedStrings.add("\t" + c.toString());
            }
            Collections.sort(sortedStrings);
            for (String s : sortedStrings) {
                this.displayMessage(s);
            }

            return this.requestCompositionString();
        }

        return compositionString;
    }

    /**
     * Requests confirmation from the user.
     *
     * @return true if user answers yes, false if user answers no
     */
    public boolean requestConfirmation(String message) {
        while (true) {
            String input = this.requestString(message + " (y/n)");

            if (input.startsWith("y")) {
                return true;
            } else if (input.startsWith("n")) {
                return false;
            }

            this.displayMessage("Please try again.");
        }
    }

    @Override
    public String requestString(String message) {
        if (this.clpi != null) {
            this.clpi.hide();
        }

        while (true) {
            this.displayMessage(message);
            
            this.displayInputMarker();
            final String input = this.scanner.nextLine();

            switch (input) {
            case "?":
            case "h":
            case "help":
                this.displayHelp();
                break;
            case "exit":
                this.core.submit(new VirageExitJob(this, 0));
                break;
            default:
                if (this.clpi != null) {
                    this.clpi.show();
                }

                return input;
            }
        }
    }
    
    private void displayInputMarker() {
        // Set background to white and text to black to signal input opportunity.
        // ">" would be nicer, but this appears to conflict with mvn exec:exec,
        // see https://github.com/mojohaus/exec-maven-plugin/issues/159.
        try {
            this.outputWriter.append("? \033[1A\n");
            this.outputWriter.flush();
        } catch (IOException e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
        }
    }

    @Override
    public void displayMessage(String message) {
        try {
            this.outputWriter.append(message + "\n");
            this.outputWriter.flush();
        } catch (IOException e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
        }
    }

    @Override
    public void displayError(String message) {
        System.err.println(message);
    }

    public void displayHelp() {
        InputStream helpStream = this.getClass().getClassLoader().getResourceAsStream("help.txt");
        StringWriter writer = new StringWriter();
        try {
            IOUtils.copy(helpStream, writer, StandardCharsets.UTF_8);
        } catch (IOException e) {
            logger.error("Something went wrong.", e);
            e.printStackTrace();
        }
        this.displayMessage(writer.toString());

        this.requestString("Press ENTER to leave help and return to previous state.");
    }

    @Override
    public int chooseAlternative(String message, List<?> alternatives) {
        this.displayMessage(message + "\n");

        for (int i = 0; i < alternatives.size(); i++) {
            this.displayMessage("[" + i + "] " + alternatives.get(i).toString());
        }

        int res;
        while (true) {
            final String input = this.requestString("Please enter a number between 0 and "
                    + (alternatives.size() - 1) + " or leave empty to choose none of the above.");

            if (input.isEmpty()) {
                return -1;
            }

            try {
                res = Integer.parseInt(input);

                if (0 <= res && res < alternatives.size()) {
                    return res;
                }
            } catch (NumberFormatException e) {
                // NO-OP
            }

            this.displayError("Please try again.");
        }
    }
}
