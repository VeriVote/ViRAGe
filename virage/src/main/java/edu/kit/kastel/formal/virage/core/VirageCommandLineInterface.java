package edu.kit.kastel.formal.virage.core;

import java.io.BufferedWriter;
import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStreamWriter;
import java.io.StringWriter;
import java.io.Writer;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedList;
import java.util.List;
import java.util.Scanner;
import java.util.Set;

import org.apache.commons.io.IOUtils;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import edu.kit.kastel.formal.util.StringUtils;
import edu.kit.kastel.formal.util.SystemUtils;
import edu.kit.kastel.formal.virage.isabelle.IsabelleUtils;
import edu.kit.kastel.formal.virage.jobs.VirageAnalyzeAllPropertiesJob;
import edu.kit.kastel.formal.virage.jobs.VirageAnalyzeJob;
import edu.kit.kastel.formal.virage.jobs.VirageDummyJob;
import edu.kit.kastel.formal.virage.jobs.VirageExitJob;
import edu.kit.kastel.formal.virage.jobs.VirageExtractJob;
import edu.kit.kastel.formal.virage.jobs.VirageGenerateCCodeJob;
import edu.kit.kastel.formal.virage.jobs.VirageGenerateJob;
import edu.kit.kastel.formal.virage.jobs.VirageIsabelleGenerateJob;
import edu.kit.kastel.formal.virage.jobs.VirageIsabelleGenerateScalaJob;
import edu.kit.kastel.formal.virage.jobs.VirageIsabelleVerifyJob;
import edu.kit.kastel.formal.virage.jobs.VirageJob;
import edu.kit.kastel.formal.virage.jobs.VirageJobState;
import edu.kit.kastel.formal.virage.jobs.VirageParseJob;
import edu.kit.kastel.formal.virage.jobs.VirageProveJob;
import edu.kit.kastel.formal.virage.prolog.JplFacade;
import edu.kit.kastel.formal.virage.prolog.PrologParser;
import edu.kit.kastel.formal.virage.types.CompositionProof;
import edu.kit.kastel.formal.virage.types.DecompositionTree;
import edu.kit.kastel.formal.virage.types.ExternalSoftwareUnavailableException;
import edu.kit.kastel.formal.virage.types.FrameworkRepresentation;
import edu.kit.kastel.formal.virage.types.InvalidConfigVersionException;
import edu.kit.kastel.formal.virage.types.Property;
import edu.kit.kastel.formal.virage.types.TypedAndParameterized;

/**
 * A simple command line interface for ViRAGe.
 *
 * @author VeriVote
 */
public final class VirageCommandLineInterface implements VirageUserInterface {
    /**
     * The logger.
     */
    private static final Logger LOGGER = LogManager.getLogger(VirageCommandLineInterface.class);

    /**
     * Linux user library path.
     */
    private static final String USR_LIB_PATH = "/usr/lib/";

    /**
     * File extension for text files.
     */
    private static final String DOT_TXT = StringUtils.DOT_CHAR + "txt";

    /**
     * File extension for .so-library files.
     */
    private static final String DOT_SO = StringUtils.DOT_CHAR + "so";

    /**
     * Name of libswipl.so.
     */
    private static final String LIBSWIPL_SO = "libswipl" + DOT_SO;

    /**
     * Name of libjpl.so.
     */
    private static final String LIBJPL_SO = "libjpl" + DOT_SO;

    /**
     * String option for expressing 'yes'.
     */
    private static final String YES = "y";

    /**
     * String option for expressing 'no'.
     */
    private static final String NO = "n";

    /**
     * The separator.
     */
    private static final String SEPARATOR = StringUtils.repeat(59, StringUtils.HASH);

    /**
     * The banner.
     */
    private static final String BANNER = StringUtils.HASH + System.lineSeparator()
            + StringUtils.HASH + " Y88b      / ,e, 888~-_        e       e88~~\\           "
            + System.lineSeparator()
            + StringUtils.HASH + "  Y88b    /   \"  888   \\      d8b     d888      e88~~8e "
            + System.lineSeparator()
            + StringUtils.HASH + "   Y88b  /   888 888    |    /Y88b    8888 __  d888  88b"
            + System.lineSeparator()
            + StringUtils.HASH + "    Y888/    888 888   /    /  Y88b   8888   | 8888__888"
            + System.lineSeparator()
            + StringUtils.HASH + "     Y8/     888 888_-~    /____Y88b  Y888   | Y888    ,"
            + System.lineSeparator()
            + StringUtils.HASH + "      Y      888 888 ~-_  /      Y88b  \"88__/   \"88___/ "
            + System.lineSeparator() + StringUtils.HASH;

    /**
     * Character to print before lines.
     */
    private static final String HEADER_LINE_START = StringUtils.addSpace(StringUtils.HASH);

    /**
     * Dialog fragment for library directory.
     */
    private static final String LIB_DIR = "library directory";

    /**
     * Dialog fragment for path input.
     */
    private static final String INPUT_PATH_MSG = "Please input the path to ";

    /**
     * Dialog fragment for your setup of something.
     */
    private static final String YOUR_SETUP_MSG = "For your setup of ";

    /**
     * Dialog fragment for your system settings.
     */
    private static final String YOUR_SYSTEM_MSG = ", but this might differ on your system.";

    /**
     * Dialog whether settings should be changed.
     */
    private static final String SETTINGS_CHANGE_MESSAGE =
            "ViRAGe can replace the settings file with an up-to-date one. "
                    + "Your old settings file will be moved to "
                    + StringUtils.addDoubleQuotes(ConfigReader.OLD_SETTINGS)
                    + ", and as many settings " + "as possible will be transferred. "
                    + "Do you want to let ViRAGe perform this operation?";

    /**
     * Message that state is unsafe.
     */
    private static final String UNSAFE_STATE_MESSAGE =
            "ViRAGe is in an unsafe state as you "
                    + "loaded an outdated configuration.";

    /**
     * Dialog whether to continue.
     */
    private static final String CONTINUE_MESSAGE = "Do you want to continue anyways?";

    /**
     * Version message.
     */
    private static final String VERSION_MESSAGE = "Version ";

    /**
     * Help string.
     */
    private static final String HELP = "help";

    /**
     * Exit string.
     */
    private static final String EXIT = "exit";

    /**
     * Help info message.
     */
    private static final String HELP_MESSAGE =
            StringUtils.appendPeriod(
                    "If you need " + HELP + ", type " + StringUtils.addDoubleQuotes(HELP)
                            + StringUtils.COMMA + StringUtils.SPACE
                            + StringUtils.or(
                                    StringUtils.addDoubleQuotes(String.valueOf(HELP.charAt(0))),
                                    StringUtils.addDoubleQuotes(StringUtils.QUESTION)));

    /**
     * Info message on how to exit.
     */
    private static final String EXIT_INFO_MESSAGE =
            StringUtils.appendPeriod("To exit ViRAGe, type " + StringUtils.addDoubleQuotes(EXIT));

    /**
     * First line of purpose message.
     */
    private static final String PURPOSE_ONE_MESSAGE =
            "# ViRAGe is a tool to generate voting rules and automatically ";

    /**
     * Second line of purpose message.
     */
    private static final String PURPOSE_TWO_MESSAGE =
            "# reason about their social choice properties.";

    /**
     * Message that SWI library could not be located.
     */
    private static final String SWI_LIBRARY_ERROR_MESSAGE =
            "A required " + PrologParser.SWI_PROLOG + " library "
                    + StringUtils.parenthesize(StringUtils.addDoubleQuotes(LIBSWIPL_SO))
                    + " could not be located.";

    /**
     * Message to ask the user to retry.
     */
    private static final String TRY_AGAIN = "Please try again.";

    /**
     * Message with ENTER for default.
     */
    private static final String ENTER_FOR_DEFAULT_MESSAGE = "Press ENTER for default: ";

    /**
     * A Scanner to read input.
     */
    private final Scanner scanner;

    /**
     * The core this UI is attached to.
     */
    private final VirageCore core;

    /**
     * Writer to display output.
     */
    private final Writer outputWriter;

    /**
     * Simple constructor.
     *
     * @param coreValue the ViRAGe core this UI will be attached to.
     */
    protected VirageCommandLineInterface(final VirageCore coreValue) {
        final int bufferSize = 4096;
        this.outputWriter =
                new BufferedWriter(new OutputStreamWriter(System.out, StandardCharsets.UTF_8),
                                   bufferSize);
        LOGGER.info("Initialising VirageCommandLineInterface.");
        this.scanner = new Scanner(System.in, StandardCharsets.UTF_8);
        this.core = coreValue;

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
    }

    private static boolean isYesNo(final String input, final boolean yesNo) {
        final String lowerCase = input.toLowerCase();
        return lowerCase.startsWith(yesNo ? YES : NO);
    }

    @Override
    public void displayMessage(final String message) {
        try {
            this.outputWriter.append(message + System.lineSeparator());
            this.outputWriter.flush();
        } catch (final IOException e) {
            e.printStackTrace();
        }
    }

    private void printSeparator() {
        this.displayMessage(SEPARATOR);
    }

    private void printBanner() {
        this.displayMessage(BANNER);
    }

    /**
     * Requests confirmation from the user.
     *
     * @return true if user answers yes, false if user answers no
     */
    @Override
    public boolean requestConfirmation(final String message) {
        while (true) {
            final String request =
                    StringUtils.printCollection2(message, StringUtils.parenthesize(YES + "/" + NO));
            final String input = this.requestString(request);
            if (isYesNo(input, true) || isYesNo(input, false)) {
                return isYesNo(input, true);
            } else {
                this.displayMessage(TRY_AGAIN);
            }
        }
    }

    private void checkSettingsCompatibility() {
        try {
            ConfigReader.getInstance().readConfigFile(false);
        } catch (final InvalidConfigVersionException e) {
            this.displayMessage(HEADER_LINE_START + e.getMessage());
            if (this.requestConfirmation(HEADER_LINE_START + SETTINGS_CHANGE_MESSAGE)) {
                try {
                    ConfigReader.getInstance().readConfigFile(true);
                } catch (final IOException | InvalidConfigVersionException e1) {
                    e1.printStackTrace();
                }
            } else {
                this.displayMessage(HEADER_LINE_START + UNSAFE_STATE_MESSAGE);
                if (!this.requestConfirmation(CONTINUE_MESSAGE)) {
                    this.core.submit(new VirageExitJob(this, 0));
                }
            }
        } catch (final IOException e) {
            e.printStackTrace();
        }
    }

    private void printTimestamp() {
        final String now = SystemUtils.getCurrentTime();
        this.displayMessage(
                StringUtils.printCollection2(HEADER_LINE_START, VERSION_MESSAGE,
                                             VirageCore.getVersion() + StringUtils.COMMA,
                                             StringUtils.addColon("Timestamp"), now));
        this.displayMessage(HEADER_LINE_START + HELP_MESSAGE);
        this.displayMessage(HEADER_LINE_START + EXIT_INFO_MESSAGE);
    }

    private void printPurpose() {
        this.displayMessage(PURPOSE_ONE_MESSAGE);
        this.displayMessage(PURPOSE_TWO_MESSAGE);
    }

    @Override
    public void displayError(final String message) {
        System.err.println(message);
    }

    private void setupLibswipl() {
        this.displayError(SWI_LIBRARY_ERROR_MESSAGE);
        String newValue;
        try {
            while (true) {
                newValue = this.requestString(
                        StringUtils.addSpace(StringUtils.appendPeriod(
                                INPUT_PATH_MSG + LIBSWIPL_SO))
                        + YOUR_SETUP_MSG + PrologParser.SWI_PROLOG + ", typical values are "
                        + StringUtils.or(
                                StringUtils.addQuotations(USR_LIB_PATH + LIBSWIPL_SO),
                                StringUtils.addQuotations(
                                        ConfigReader.getInstance().getSwiplLib() + LIBSWIPL_SO))
                        + YOUR_SYSTEM_MSG);
                if (!newValue.isEmpty()) {
                    final File file = SystemUtils.file(newValue);
                    if (!file.exists()) {
                        this.displayError("This file does not exist. " + TRY_AGAIN);
                        continue;
                    }
                    if (!newValue.endsWith(LIBSWIPL_SO)) {
                        this.displayError(StringUtils.appendPeriod(
                                "This is not " + StringUtils.addDoubleQuotes(LIBSWIPL_SO))
                                + StringUtils.SPACE + TRY_AGAIN);
                        continue;
                    }
                    ConfigReader.getInstance().updateValueForLibswiplPath(newValue);
                    break;
                }
            }
        } catch (final ExternalSoftwareUnavailableException e1) {
            e1.printStackTrace();
        }
    }

    private void setubLibjpl() {
        this.displayError("The " + PrologParser.SWI_PROLOG
                + StringUtils.SPACE + LIB_DIR + " could not be located. "
                + "This directory must contain the library "
                + StringUtils.addDoubleQuotes(LIBJPL_SO)
                + ", otherwise ViRAGe will not work properly.");
        String newValue;
        try {
            while (true) {
                newValue = this.requestString(
                        StringUtils.appendPeriod(INPUT_PATH_MSG + "the " + PrologParser.SWI_PROLOG
                                + StringUtils.SPACE + LIB_DIR) + StringUtils.SPACE
                        + YOUR_SETUP_MSG + PrologParser.SWI_PROLOG + ", the typical value is "
                        + StringUtils.addQuotations(ConfigReader.getInstance().getSwiplLib())
                        + YOUR_SYSTEM_MSG);
                if (!newValue.isEmpty()) {
                    final File file = SystemUtils.file(newValue);
                    if (!file.exists()) {
                        this.displayError("This directory does not exist. " + TRY_AGAIN);
                        continue;
                    } else if (!file.isDirectory()) {
                        this.displayError("This path is not a directory. " + TRY_AGAIN);
                        continue;
                    } else if (!(SystemUtils.file(newValue + File.separator + LIBJPL_SO)
                                    .exists())) {
                        this.displayError(
                                StringUtils.appendPeriod(
                                        "This directory does not contain "
                                                + StringUtils.addDoubleQuotes(LIBJPL_SO))
                                + " You either supplied the wrong directory, "
                                + "or JPL is not installed.");
                        continue;
                    }
                    ConfigReader.getInstance().updateValueForSwiPrologLibrariesPath(newValue);
                    break;
                }
            }
        } catch (final ExternalSoftwareUnavailableException e1) {
            e1.printStackTrace();
        }
    }

    private void checkEnvironment() {
        this.displayMessage(HEADER_LINE_START + ConfigReader.getInstance()
                .checkAvailabilityAndGetVersions()
                .replace(System.lineSeparator(),
                         System.lineSeparator() + StringUtils.addSpace(StringUtils.HASH)));
        boolean unsafeState = false;
        try {
            /* As far as I remember, this just collects potential exceptions from attempting to
             * construct JPL. */
            new JplFacade();
        } catch (final ExternalSoftwareUnavailableException e) {
            this.setupLibswipl();
            unsafeState = true;
        } catch (final UnsatisfiedLinkError e) {
            this.setubLibjpl();
            unsafeState = true;
        }
        if (unsafeState) {
            this.displayMessage("A restart is required for the changes to take effect. "
                    + "Please restart ViRAGe after it terminated.");
            SystemUtils.exit(0);
        }
    }

    private void printSettings() {
        this.displayMessage(HEADER_LINE_START + "Reading configuration from "
                + StringUtils.addQuotations(ConfigReader.getConfigPath()) + StringUtils.COMMA);
        this.displayMessage(HEADER_LINE_START + "the following settings were found:");
        final List<String> propertyNames = new LinkedList<String>();
        for (final String s: ConfigReader.getInstance().getAllProperties().keySet()) {
            propertyNames.add(s);
        }
        Collections.sort(propertyNames);
        String lastPrefix = StringUtils.EMPTY;
        final String prefixSeparator = "_";
        for (final String s: propertyNames) {
            if (!lastPrefix.equals(s.split(prefixSeparator)[0])) {
                this.displayMessage(StringUtils.HASH);
                lastPrefix = s.split(prefixSeparator)[0];
            }
            String value =
                    ConfigReader.getInstance().getAllProperties().get(s)
                        .replaceAll(ConfigReader.LIST_SEPARATOR, ";\n#\t");
            if (value.isEmpty()) {
                value = "NOT_SET";
            }
            this.displayMessage(HEADER_LINE_START + s.toUpperCase() + StringUtils.COLON
                                + System.lineSeparator() + StringUtils.HASH + StringUtils.TAB
                                + value);
        }
        if (!propertyNames.isEmpty()) {
            this.displayMessage(HEADER_LINE_START);
        }
        if (this.requestConfirmation(HEADER_LINE_START + "Do you want to edit these settings? "
                + "This will open the configuration file via "
                + StringUtils.addQuotations(ConfigReader.XDG_OPEN) + " or your chosen text editor"
                + " and require a restart of ViRAGe.")) {
            try {
                this.displayMessage(HEADER_LINE_START
                        + "If ViRAGe freezes or terminates without opening an editor, "
                        + "please try another one by setting "
                        + StringUtils.addDoubleQuotes(ConfigReader.SYSTEM_EDITOR)
                        + " in " + ConfigReader.getConfigPath()
                        + ". At the moment, only windowed "
                        + "editors (mousepad, ...) are supported, not in-terminal ones "
                        + "(nano, vim, ...).");
                ConfigReader.getInstance().openConfigFileForEditing();
                this.displayMessage(HEADER_LINE_START
                        + "Please restart ViRAGe for the changes to take effect.");
                SystemUtils.exit(0);
            } catch (final ExternalSoftwareUnavailableException e) {
                this.displayMessage(
                        HEADER_LINE_START + "No text editor available. "
                        + StringUtils.appendPeriod(
                                "Please set the configuration option "
                                        + StringUtils.addDoubleQuotes(ConfigReader.SYSTEM_EDITOR)
                                        + " or the environment variable "
                                        + StringUtils.addDoubleQuotes(ConfigReader.EDITOR)));
            }
        }
    }

    /**
     * Display help from resources/help.txt.
     */
    public void displayHelp() {
        final InputStream helpStream =
                this.getClass().getClassLoader().getResourceAsStream(HELP + DOT_TXT);
        final StringWriter writer = new StringWriter();
        try {
            IOUtils.copy(helpStream, writer, StandardCharsets.UTF_8);
        } catch (final IOException e) {
            LOGGER.error("Something went wrong.", e);
            e.printStackTrace();
        }
        this.displayMessage(writer.toString());
        this.requestString("Press ENTER to leave " + HELP + " and return to previous state.");
    }

    private void displayInputMarker() {
        try {
            this.outputWriter.append(
                    StringUtils.printCollection2(
                            StringUtils.repeat(StringUtils.TEN, StringUtils.PERIOD), "\033[1A")
                            + System.lineSeparator());
            this.outputWriter.flush();
        } catch (final IOException e) {
            e.printStackTrace();
        }
    }

    @Override
    public String requestString(final String message) {
        while (true) {
            this.displayMessage(message);
            this.displayInputMarker();
            final String input = this.scanner.nextLine();
            switch (input) {
            case StringUtils.QUESTION, "h", "H", HELP:
                this.displayHelp();
                break;
            case "x", "X", "q", "Q", EXIT:
                this.core.submit(new VirageExitJob(this, 0));
                break;
            default:
                return input;
            }
        }
    }

    @Override
    public int chooseAlternative(final String message, final List<?> alternatives,
                                 final boolean allowChoosingNone) {
        this.displayMessage(message + System.lineSeparator());
        for (int i = 0; i < alternatives.size(); i++) {
            this.displayMessage("[" + i + "] " + alternatives.get(i).toString());
        }
        int res;
        while (true) {
            String requestMessage =
                    "Please enter a number between 0 and " + (alternatives.size() - 1);
            if (allowChoosingNone) {
                requestMessage += " or leave empty to choose none of the above.";
            } else {
                requestMessage = StringUtils.appendPeriod(requestMessage);
            }
            final String input = this.requestString(requestMessage);
            if (input.isEmpty()) {
                if (allowChoosingNone) {
                    return -1;
                }
            }
            try {
                res = Integer.parseInt(input);
                if (0 <= res && res < alternatives.size()) {
                    return res;
                }
            } catch (final NumberFormatException e) {
                // NO-OP
            }
            this.displayError(TRY_AGAIN + System.lineSeparator());
        }
    }

    /**
     * Request the property string.
     * TODO: Change to return type to <code>List&lt;Property&gt;</code>, maybe?
     *
     * @return the property string.
     */
    private String requestPropertyString() {
        final FrameworkRepresentation framework = this.core.getFrameworkRepresentation();
        String propertiesString =
                this.requestString("Please input the desired "
                                    + "properties (separated by '" + StringUtils.COMMA + "') or "
                                    + "leave empty to display available properties.");
        propertiesString = StringUtils.removeWhitespace(propertiesString);
        boolean invalid = false;
        if (!propertiesString.isEmpty()) {
            final String[] propertyStrings = propertiesString.split(StringUtils.COMMA);
            for (final String propertyString: propertyStrings) {
                final Property property = framework.getProperty(propertyString);
                if (property == null) {
                    LOGGER.error("Property " + StringUtils.addDoubleQuotes(propertyString)
                                + " is undefined.");
                    invalid = true;
                    break;
                }
            }
        }
        if (propertiesString.isEmpty() || invalid) {
            final List<String> sortedProps = new ArrayList<String>();
            for (final Property p: this.core.getFrameworkRepresentation().getProperties()) {
                if (p.getArity() == 1 && !p.isAtomic()) {
                    sortedProps.add(StringUtils.indentWithTab(p.getName()));
                }
            }
            Collections.sort(sortedProps);
            for (final String s: sortedProps) {
                this.displayMessage(s);
            }
            return this.requestPropertyString();
        }
        return propertiesString;
    }

    private static List<String> convertNames(final Set<? extends TypedAndParameterized> cs) {
        final List<String> names = new ArrayList<String>(cs.size());
        for (final TypedAndParameterized c: cs) {
            names.add(StringUtils.indentWithTab(c.toString()));
        }
        return names;
    }

    private String requestCompositionString() {
        boolean invalid = false;
        String compositionString = this
                .requestString("Please input a composition "
                        + StringUtils.parenthesize("in Prolog format")
                        + " or leave empty to display available components.");
        compositionString = StringUtils.removeWhitespace(compositionString);
        if (!compositionString.isEmpty()) {
            try {
                final DecompositionTree tree = DecompositionTree.parseString(compositionString);
                tree.fillMissingVariables(this.core.getFrameworkRepresentation());
                this.displayMessage("Interpreted input as " + tree.toString() + StringUtils.PERIOD);
                return tree.toString();
            } catch (final IllegalArgumentException e) {
                LOGGER.error(StringUtils.addDoubleQuotes(compositionString)
                            + " could not be parsed. Please check the brackets and try again.");
                invalid = true;
            }
        }
        if (compositionString.isEmpty() || invalid) {
            final FrameworkRepresentation fr = this.core.getFrameworkRepresentation();
            final List<String> compNames = convertNames(fr.getComponents());
            final List<String> modNames = convertNames(fr.getComposableModules());
            final List<String> structNames = convertNames(fr.getCompositionalStructures());
            final List<String> sortedStrings =
                    new ArrayList<String>(compNames.size() + modNames.size() + structNames.size());

            sortedStrings.addAll(compNames);
            sortedStrings.addAll(modNames);
            sortedStrings.addAll(structNames);
            Collections.sort(sortedStrings);
            for (final String s: sortedStrings) {
                this.displayMessage(s);
            }
            return this.requestCompositionString();
        }
        return compositionString;
    }

    private VirageAnalyzeJob createAnalysisQuery() {
        final String composition = this.requestCompositionString();
        final String propertyString = this.requestPropertyString();
        final List<String> properties = StringUtils.separate(StringUtils.COMMA, propertyString);
        return new VirageAnalyzeJob(this, composition, properties);
    }

    private VirageGenerateCCodeJob createCCodeGenerationQuery() {
        final String composition = this.requestCompositionString();
        return new VirageGenerateCCodeJob(this, composition);
    }

    private VirageIsabelleGenerateScalaJob createCodeGenerationQuery() {
        final String composition = this.requestCompositionString();
        return new VirageIsabelleGenerateScalaJob(this, composition);
    }

    private VirageGenerateJob createGenerationQuery() {
        final String propertyString = this.requestPropertyString();
        final List<String> properties = StringUtils.separate(StringUtils.COMMA, propertyString);
        return new VirageGenerateJob(this, properties);
    }

    private VirageProveJob createProofQuery(final String composition, final String propertyString) {
        final List<String> properties = StringUtils.separate(StringUtils.COMMA, propertyString);
        return new VirageProveJob(this, composition, properties);
    }

    private VirageJob<?> createIsabelleQuery() {
        final String composition = this.requestCompositionString();
        final String propertyString = this.requestPropertyString();
        final String defaultPath = ConfigReader.getInstance().getDefaultOutputPath();
        String outputPath = this.requestString("Please specify a directory for the "
                + "generated theory file."
                + StringUtils.parenthesize(
                        ENTER_FOR_DEFAULT_MESSAGE + StringUtils.addQuotations(defaultPath)));
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
        final VirageProveJob proveJob = this.createProofQuery(composition, propertyString);
        this.core.submit(proveJob);
        proveJob.waitFor();
        if (proveJob.getState() == VirageJobState.FAILED) {
            LOGGER.warn("Proving the given claims failed.");
            return new VirageDummyJob(this);
        }
        final List<List<CompositionProof>> proofLists = proveJob.getResult();
        List<CompositionProof> bestProof = new LinkedList<CompositionProof>();
        for (final List<CompositionProof> proof: proofLists) {
            if (proof.size() > bestProof.size()) {
                bestProof = proof;
            }
        }
        final VirageIsabelleGenerateJob generateJob =
                new VirageIsabelleGenerateJob(this, composition, bestProof, outputPath);
        if (!verify) {
            return generateJob;
        }
        this.core.submit(generateJob);
        generateJob.waitFor();
        return new VirageIsabelleVerifyJob(this, generateJob.getResult());
    }

    /**
     * Parse and submit the ViRAGe job, and then wait for and return the result.
     * @param path the result path of the ViRAGe job
     * @return the job result
     */
    private FrameworkRepresentation parseAndSubmitJob(final String path) {
        final VirageParseJob parseJob = new VirageParseJob(this, SystemUtils.file(path));
        this.displayMessage("The following operation might take some time, "
                + "especially when ViRAGe is run with previously " + "un-built Isabelle sessions.");
        this.core.submit(parseJob);
        parseJob.waitFor();
        // Inelegant, but prevents race condition where user prompt is printed before the result.
        SystemUtils.semiBusyWaitingHelper();
        final FrameworkRepresentation toReturn;
        switch (parseJob.getState()) {
        case FINISHED:
            toReturn = parseJob.getResult();
            break;
        default:
            toReturn = null;
        }
        return toReturn;
    }

    private String findSessionName(final String path) throws IOException {
        final String sessionName;
        final List<String> sessionNames =
                IsabelleUtils.getSessionNamesFromRootFile(
                        SystemUtils.file(path + File.separator + IsabelleUtils.ROOT)
                        );
        if (sessionNames.isEmpty()) {
            this.displayError("No sessions found in the " + IsabelleUtils.ROOT + " file!");
            return null;
        } else if (sessionNames.size() == 1) {
            sessionName = sessionNames.get(0);
            this.displayMessage("Found only one session, "
                            + StringUtils.addDoubleQuotes(sessionName) + ", this will be used.");
        } else {
            final int sessionNameIndex =
                    this.chooseAlternative(
                            "Which of the following sessions specified in the "
                                    + IsabelleUtils.ROOT + " file shall be used?",
                            sessionNames, false);
            sessionName = sessionNames.get(sessionNameIndex);
        }
        return sessionName;
    }

    private String getNewFileName(final String path) {
        String newFileName;
        while (true) {
            newFileName = this.requestString("Please enter a name for the new file.");
            if (newFileName.isBlank()) {
                this.displayMessage("An empty file name is not allowed.");
                continue;
            }
            if (!newFileName.endsWith(PrologParser.DOT_PL)) {
                newFileName += PrologParser.DOT_PL;
            }
            final File checkExistenceFile = SystemUtils.file(path + File.separator + newFileName);
            if (!checkExistenceFile.exists()) {
                break;
            } else if (this.requestConfirmation(
                    "File exists already. " + "Do you want to overwrite it?")) {
                break;
            }
        }
        return newFileName;
    }

    private FrameworkRepresentation extractAndOrParseFramework(final String passedPath)
            throws IOException, ExternalSoftwareUnavailableException {
        String path = passedPath;
        if (!path.endsWith(PrologParser.DOT_PL)) {
            if (path.endsWith(IsabelleUtils.ROOT)) {
                path = path.substring(0, path.length() - IsabelleUtils.ROOT.length());
            }
            final File file = SystemUtils.file(path);
            String newFileName = null;
            if (file.isDirectory()) {
                final List<File> plFiles = new LinkedList<File>();
                final File[] files = file.listFiles();
                if (files != null) {
                    for (final File child: files) {
                        if (child != null
                                && child.getAbsolutePath().endsWith(PrologParser.DOT_PL)) {
                            plFiles.add(child);
                        }
                    }
                }
                if (!plFiles.isEmpty()) {
                    final int idx = this.chooseAlternative(
                            "The following " + PrologParser.EPL_FILE + "s "
                            + StringUtils.parenthesize(PrologParser.DOT_PL) + " were found. "
                            + "Do you want to use one of those and skip " + PrologParser.EPL_FILE
                            + StringUtils.SPACE + StringUtils.parenthesize(PrologParser.DOT_PL)
                            + " generation? "
                            + "This saves time if no changes to the Isabelle theories were "
                            + "made since the " + PrologParser.EPL_FILE + StringUtils.SPACE
                            + StringUtils.parenthesize(PrologParser.DOT_PL) + " was created.",
                            plFiles, true);
                    if (idx != -1) {
                        return this.extractAndOrParseFramework(plFiles.get(idx).getAbsolutePath());
                    } else {
                        newFileName = this.getNewFileName(path);
                    }
                }
            }

            if (!ConfigReader.getInstance().hasIsabelle()) {
                this.displayMessage("Isabelle is not available. "
                        + "Please install Isabelle or supply an " + PrologParser.EPL_FILE
                        + StringUtils.SPACE
                        + StringUtils.parenthesize(PrologParser.DOT_PL) + " directly.");
                throw new ExternalSoftwareUnavailableException();
            }
            final VirageExtractJob extractJob =
                    new VirageExtractJob(this, path, this.findSessionName(path), newFileName);
            this.core.submit(extractJob);
            extractJob.waitFor();
            switch (extractJob.getState()) {
            case FAILED:
                return null;
            default: // go on
            }
            path = extractJob.getResult().getAbsolutePath();
        }
        return parseAndSubmitJob(path);
    }

    /**
     * Extract paths, collect inputs, and parse data for running further jobs.
     */
    private void extractOrParseInputs() {
        final String defaultPath = "./" + SystemUtils.RESOURCES + "framework" + PrologParser.DOT_PL;
        String path;
        boolean firstTry = true;
        while (true) {
            if (ConfigReader.getInstance().hasPathToRootFile() && firstTry
                    && this.requestConfirmation(
                            StringUtils.appendPeriod(
                                    "Configuration option "
                                    + StringUtils.addDoubleQuotes(ConfigReader.ROOT_FILE_PATH)
                                    + " is specified as "
                                    + StringUtils.addQuotations(
                                            ConfigReader.getInstance().getPathToRootFile()))
                                    + StringUtils.SPACE
                                    + StringUtils.appendQuestionMark(
                                            "Do you want to use this Isabelle " + IsabelleUtils.ROOT
                                            + " file to generate an " + PrologParser.EPL_FILE
                                            + StringUtils.SPACE
                                    + StringUtils.parenthesize(PrologParser.DOT_PL)))) {
                path = ConfigReader.getInstance().getPathToRootFile();
                firstTry = false;
            } else {
                path = this.requestString(INPUT_PATH_MSG
                        + "an " + PrologParser.EPL_FILE + " or an Isabelle " + IsabelleUtils.ROOT
                        + " file. "
                        + StringUtils.parenthesize(ENTER_FOR_DEFAULT_MESSAGE
                                                    + StringUtils.addQuotations(defaultPath)));
            }
            if (path.isEmpty()) {
                path = defaultPath;
            }
            try {
                if (this.extractAndOrParseFramework(path) != null) {
                    break;
                }
            } catch (final IOException | ExternalSoftwareUnavailableException e) {
                e.printStackTrace();
            }
        }
    }

    /**
     * Similar to run(), but creates its own new thread.
     */
    @Override
    public void launch() {
        new Thread(this, "vcli").start();
    }

    @Override
    public void notify(final VirageJob<?> job) {
        this.displayMessage(job.presentResult() + System.lineSeparator());
    }

    @Override
    public void run() {
        LOGGER.info("Started VirageCommandLineInterface.");
        extractOrParseInputs();
        while (true) {
            final String arg = this
                    .requestString("Do you want to (g)enerate a composition, (a)nalyze one, "
                            + "run an (A)nalysis of all properties for a composition, "
                            + "generate Isabelle (p)roofs, generate (S)cala code "
                            + "or generate (C) code?").strip();
            final VirageJob<?> job;
            switch (arg.substring(0, arg.isEmpty() ? 0 : 1)) {
            case "g":
                job = this.createGenerationQuery();
                break;
            case "a":
                job = this.createAnalysisQuery();
                break;
            case "p":
                job = this.createIsabelleQuery();
                break;
            case "S":
                job = this.createCodeGenerationQuery();
                break;
            case "C":
                job = this.createCCodeGenerationQuery();
                break;
            case "A":
                job = new VirageAnalyzeAllPropertiesJob(this, this.requestCompositionString());
                break;
            default:
                this.displayMessage(TRY_AGAIN);
                job = null;
                continue;
            }
            this.core.submit(job);
            // VirageCore is intended to work on jobs asynchronously
            // and that is perfectly possible. It just does not make
            // too much sense when using a CLI, so it is disabled.
            job.waitFor();
        }
    }
}
