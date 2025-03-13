package edu.kit.kastel.formal.virage.core;

import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.io.StringWriter;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Properties;

import org.apache.commons.configuration2.Configuration;
import org.apache.commons.configuration2.FileBasedConfiguration;
import org.apache.commons.configuration2.PropertiesConfiguration;
import org.apache.commons.configuration2.builder.FileBasedConfigurationBuilder;
import org.apache.commons.configuration2.builder.fluent.Parameters;
import org.apache.commons.configuration2.ex.ConfigurationException;
import org.apache.commons.io.IOUtils;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import org.jpl7.JPL;

import com.google.common.collect.Maps;

import edu.kit.kastel.formal.util.Pair;
import edu.kit.kastel.formal.util.ProcessUtils;
import edu.kit.kastel.formal.util.SimpleFileReader;
import edu.kit.kastel.formal.util.SimpleFileWriter;
import edu.kit.kastel.formal.util.StringUtils;
import edu.kit.kastel.formal.util.SystemUtils;
import edu.kit.kastel.formal.virage.prolog.PrologParser;
import edu.kit.kastel.formal.virage.types.ExternalSoftwareUnavailableException;
import edu.kit.kastel.formal.virage.types.InvalidConfigVersionException;

/**
 * A class to interact with a ViRAGe configuration file.
 *
 * @author VeriVote
 */
public final class ConfigReader {
    /**
     * Character used to separate lists in the settings file.
     */
    public static final String LIST_SEPARATOR = ";";

    /**
     * The environment variable containing the default text editor.
     */
    protected static final String EDITOR = "EDITOR";

    /**
     * Name of the option containing the system text editor.
     */
    protected static final String SYSTEM_EDITOR = "SYSTEM_TEXT_" + EDITOR;

    /**
     * The free-desktop open command. Maybe only makes real sense for Unix systems, but well.
     */
    protected static final String XDG_OPEN = "xdg-open";

    /**
     * Name of the option containing the path to a ROOT file.
     */
    protected static final String ROOT_FILE_PATH = "ISABELLE_PATH_TO_ROOT_FILE";

    /**
     * Name of the settings file.
     */
    private static final String SETTINGS = "settings.properties";

    /**
     * Prefix for the old settings file.
     */
    private static final String OLD_PREFIX = "old_";

    /**
     * File with old settings.
     */
    protected static final String OLD_SETTINGS = OLD_PREFIX + SETTINGS;

    /**
     * The logger.
     */
    private static final Logger LOGGER = LogManager.getRootLogger();

    /**
     * The separator between keys and values.
     */
    private static final String KEY_VALUE_SEPARATOR = "=";

    /**
     * The separator for mappings.
     */
    private static final String PAIR_SEPARATOR = "->";

    /**
     * The default settings folder name.
     */
    private static final String VIRAGE_FOLDER = ".virage";

    /**
     * The user.home system property.
     */
    private static final String USER_HOME = "user.home";

    /**
     * Name of the option containing the Isabelle binary.
     */
    private static final String ISABELLE_BIN = "ISABELLE_EXECUTABLE";

    /**
     * Name of the option containing the ViRAGe configuration file version.
     */
    private static final String VIRAGE_CONFIG_VERSION = "VIRAGE_CONFIG_VERSION";

    /**
     * Name of the option containing the SWI-Prolog binary.
     */
    private static final String SWIPL_BIN = "SWI_PROLOG_EXECUTABLE";

    /**
     * Name of the option containing the GCC binary.
     */
    private static final String GCC_BIN = "GCC_EXECUTABLE";

    /**
     * Name of the option containing the Isabelle home directory.
     */
    private static final String ISABELLE_HOME = "ISABELLE_HOME";

    /**
     * Name of the option containing the user's Isabelle home directory.
     */
    private static final String ISABELLE_HOME_USER = "ISABELLE_HOME_USER";

    /**
     * Name of the option containing session specific component aliases.
     */
    private static final String COMPONENT_ALIASES = "SESSION_SPECIFIC_COMPONENT_ALIASES";

    /**
     * Name of the option containing the specified Isabelle tactics.
     */
    private static final String ISABELLE_TACTICS = "ISABELLE_TACTICS";

    /**
     * Name of the option containing type aliases.
     */
    private static final String SESSION_SPECIFIC_TYPE_ALIASES = "SESSION_SPECIFIC_TYPE_ALIASES";

    /**
     * Name of the option containing session specific assumptions.
     */
    private static final String SESSION_SPECIFIC_ASSUMPTIONS = "SESSION_SPECIFIC_ASSUMPTIONS";

    /**
     * Name of the option containing session specific atomic types.
     */
    private static final String SESSION_SPECIFIC_ATOMIC_TYPES = "SESSION_SPECIFIC_ATOMIC_TYPES";

    /**
     * Name of the option containing the default output path.
     */
    private static final String SYSTEM_DEFAULT_OUTPUT_PATH = "SYSTEM_DEFAULT_OUTPUT_PATH";

    /**
     * Name of the option containing session specific type synonyms.
     */
    private static final String SESSION_SPECIFIC_TYPE_SYNONYMS = "SESSION_SPECIFIC_TYPE_SYNONYMS";

    /**
     * Name of the option containing the time stamp.
     */
    private static final String TIMESTAMP = "TIMESTAMP";

    /**
     * SWI-Prolog option to dump runtime variables.
     */
    private static final String DUMP_RUNTIME_VARIABLES = "--dump-runtime-variables";

    /**
     * The option containing the Prolog runtime variable "<code>PLBASE</code>".
     */
    private static final String PLBASE = "PLBASE";

    /**
     * The option containing the Prolog runtime variable "<code>PLLIBDIR</code>".
     */
    private static final String PLLIBDIR = "PLLIBDIR";

    /**
     * The option containing the Prolog runtime variable "<code>PLARCH</code>".
     */
    private static final String PLARCH = "PLARCH";

    /**
     * The get environment ("<code>getenv</code>") command for Unix systems.
     */
    private static final String GET_ENVIRONMENT_CMD = "getenv";

    /**
     * Name of the option containing the Prolog libraries' path.
     */
    private static final String SWI_PROLOG_LIBRARIES_PATH = "SWI_PROLOG_LIBRARIES_PATH";

    /**
     * Name of the option containing the Prolog path.
     */
    private static final String SWI_PROLOG_LIBSWIPL_PATH = "SWI_PROLOG_LIBSWIPL_PATH";

    /**
     * Singleton instance.
     */
    private static ConfigReader instance;

    /**
     * Path to the settings file.
     */
    private static String configPath;

    /**
     * Path to the settings directory.
     */
    private static String virageFolderPath;

    /**
     * True iff Isabelle is available.
     */
    private boolean isabelleAvailable = true;

    /**
     * True iff SWI-Prolog is available.
     */
    private boolean swiplAvailable = true;

    /**
     * True iff JPL is available.
     */
    private boolean jplAvailable = true;

    /**
     * Isabelle home directory.
     */
    private String isabelleHome;

    /**
     * SWI-Prolog home directory.
     */
    private String swiplHome;

    /**
     * SWI-Prolog library directory.
     */
    private String swiplLib;

    /**
     * Isabelle session directory.
     */
    private String isabelleSessionDir;

    /**
     * The properties within the settings file.
     */
    private Properties properties;

    /**
     * The settings file.
     */
    private File configFile;

    private ConfigReader() {
        virageFolderPath =
                System.getProperty(USER_HOME) + File.separator + VIRAGE_FOLDER + File.separator;
        configPath = virageFolderPath + SETTINGS;
        // This is only to ensure unit-tests are working.
        try {
            this.readConfigFile(false);
        } catch (final IOException | InvalidConfigVersionException e) {
            // Nothing to be done
        }
    }

    /**
     * Simple getter.
     * @return the configuration file path
     */
    public static String getConfigPath() {
        virageFolderPath =
                System.getProperty(USER_HOME) + File.separator + VIRAGE_FOLDER + File.separator;
        configPath = virageFolderPath + SETTINGS;
        return configPath;
    }

    /**
     * Creates instance if necessary, otherwise just returns it.
     *
     * @return the instance
     */
    public static ConfigReader getInstance() {
        if (instance == null) {
            instance = new ConfigReader();
        }
        return instance;
    }

    private static String getVersionString(final String dependency, final String suffix,
                                           final String version, final int numberOfTabs) {
        final String suffixString =
                suffix != null && !suffix.isEmpty()
                ? StringUtils.prefixSpace(suffix) : StringUtils.EMPTY;
        final String leftColumn = StringUtils.addColon(dependency + suffixString);
        final String rightColumn = version + System.lineSeparator();
        if (0 < numberOfTabs) {
            return leftColumn + StringUtils.indentWithTabs(numberOfTabs, rightColumn);
        } else {
            return StringUtils.printCollection2(leftColumn, rightColumn);
        }
    }

    /**
     * Short-hand method for the command output within the command line interface.
     *
     * @param command the given command
     * @param option the option given as parameter for the command
     * @return the printed command output
     * @throws IOException exception in case the process yields I/O problems
     * @throws InterruptedException exception in case the process is interrupted
     */
    private static String getCommandOutput(final String command, final String option)
            throws IOException, InterruptedException {
        final String none = "<NONE>";
        final String proc = command + StringUtils.prefixSpace(option);
        final ProcessUtils.Output output = ProcessUtils.runTerminatingProcess(proc);
        final String result = output.stdOut.isEmpty() ? output.stdErr : output.stdOut;
        return result.isEmpty() ? none : result.trim();
    }

    /**
     * Checks whether all external software is available and prints the version numbers of said
     * software.
     * @return string representation of all software and versions
     */
    public String checkAvailabilityAndGetVersions() {
        final String notFound = "NOT FOUND";
        final String versionOpt = "version";
        String res = StringUtils.addColon("External dependency versions")
                    + System.lineSeparator() + System.lineSeparator();
        // JAVA
        res += getVersionString("Java", null,
                                System.getProperty(StringUtils.appendPeriod("java") + versionOpt),
                                StringUtils.THREE);
        // ISABELLE and SCALA
        final String isa = "Isabelle";
        String isaVersion;
        String scalaVersion;
        String scalaSuffix;
        try {
            final String isaExec = this.getIsabelleExecutable();
            isaVersion = getCommandOutput(isaExec, versionOpt);
            scalaVersion = getCommandOutput(StringUtils.printCollection2(isaExec, "scalac"),
                                            StringUtils.DASH + versionOpt);
            scalaSuffix = StringUtils.parenthesize2("via", isa);
        } catch (final
                IOException | InterruptedException | ExternalSoftwareUnavailableException e) {
            this.isabelleAvailable = false;
            isaVersion = notFound;
            scalaVersion = notFound;
            scalaSuffix = StringUtils.EMPTY;
            e.printStackTrace();
        }
        res += getVersionString(isa, null, isaVersion, 2);
        res += getVersionString("Scala", scalaSuffix, scalaVersion, this.isabelleAvailable ? 0 : 2);
        // SWIPL and JPL
        String swiplVersion;
        try {
            swiplVersion = getCommandOutput((String)this.properties.get(SWIPL_BIN),
                                            StringUtils.repeat(2, StringUtils.DASH) + versionOpt);
        } catch (final IOException | InterruptedException e) {
            e.printStackTrace();
            this.swiplAvailable = false;
            this.jplAvailable = false;
            swiplVersion = notFound;
        }
        res += getVersionString(PrologParser.SWI_PROLOG, null, swiplVersion, 2);
        try {
            this.getSwiplHome();
            this.getSwiplLib();
        } catch (final ExternalSoftwareUnavailableException e) {
            this.jplAvailable = false;
            this.swiplAvailable = false;
        }
        return res + getVersionString("JPL", null, JPL.version_string(), StringUtils.THREE);
    }

    private Pair<Boolean, List<String>> checkConfigCompatibility() throws IOException {
        final Properties oldProperties = new Properties();
        try (InputStream fis = java.nio.file.Files.newInputStream(this.configFile.toPath())) {
            oldProperties.load(fis);
        } catch (IOException e) {
            e.printStackTrace();
        }
        final Properties newProperties = new Properties();
        try (InputStream is = this.getClass().getClassLoader().getResourceAsStream(SETTINGS)) {
            newProperties.load(is);
        } catch (IOException e) {
            e.printStackTrace();
        }
        final List<String> missingKeys = new LinkedList<String>();
        outer: for (final Object newKey: newProperties.keySet()) {
            for (final Object oldKey: oldProperties.keySet()) {
                if (newKey.toString().equals(oldKey.toString())) {
                    continue outer;
                }
            }
            missingKeys.add(newKey.toString());
        }
        return new Pair<Boolean, List<String>>(missingKeys.isEmpty(), missingKeys);
    }

    private String computeIsabelleHome()
            throws IOException, InterruptedException, ExternalSoftwareUnavailableException {
        final String output =
                getCommandOutput(this.getIsabelleExecutable(),
                                 StringUtils.printCollection2(GET_ENVIRONMENT_CMD, ISABELLE_HOME));
        return output.split(KEY_VALUE_SEPARATOR)[1].trim();
    }

    private String computeIsabelleSessionDir()
            throws IOException, InterruptedException, ExternalSoftwareUnavailableException {
        final String output =
                getCommandOutput(this.getIsabelleExecutable(),
                                 StringUtils.printCollection2(GET_ENVIRONMENT_CMD,
                                                              ISABELLE_HOME_USER));
        return output.split(KEY_VALUE_SEPARATOR)[1].trim();
    }

    /**
     * Copies settings from <code>src/resources</code> to <code>$USER_HOME/.virage</code>.
     * @throws IOException if input/output fails
     */
    public void copyConfigToExpectedPath() throws IOException {
        final SimpleFileReader reader = new SimpleFileReader();
        final SimpleFileWriter writer = new SimpleFileWriter();
        final File oldPropertiesFile = SystemUtils.file(virageFolderPath + OLD_PREFIX + SETTINGS);
        if (!oldPropertiesFile.exists()) {
            Files.createFile(oldPropertiesFile.toPath());
        }
        writer.writeToFile(oldPropertiesFile.getAbsolutePath(), reader.readFile(this.configFile));
        final Properties oldProperties = new Properties();
        try (InputStream fis = java.nio.file.Files.newInputStream(oldPropertiesFile.toPath())) {
            oldProperties.load(fis);
        } catch (IOException e) {
            e.printStackTrace();
        }
        final InputStream configFromResourcesStream =
                this.getClass().getClassLoader().getResourceAsStream(SETTINGS);
        final StringWriter stringWriter = new StringWriter();
        IOUtils.copy(configFromResourcesStream, stringWriter, StandardCharsets.UTF_8);
        writer.writeToFile(this.configFile.getAbsolutePath(), stringWriter.toString());
        final Properties newProperties = new Properties();
        try (InputStream fis = java.nio.file.Files.newInputStream(this.configFile.toPath())) {
            newProperties.load(fis);
        }
        for (final Object o: oldProperties.keySet()) {
            final String propName = o.toString();
            if (VIRAGE_CONFIG_VERSION.equals(propName)) {
                continue;
            }
            if (newProperties.keySet().contains(o)) {
                this.updateValue(propName, oldProperties.getProperty(propName));
            }
        }
    }

    /**
     * Simple getter.
     * @return the additional properties.
     */
    public List<String> getAdditionalProperties() {
        String prop = this.properties.getProperty(SESSION_SPECIFIC_ASSUMPTIONS);
        prop = this.replaceTypeAliases(prop);
        return readAndSplitList(prop);
    }

    /**
     * Returns all defined properties.
     * @return the properties
     */
    public Map<String, String> getAllProperties() {
        final Properties props = this.properties;
        final Map<String, String> result = Maps.newHashMapWithExpectedSize(props.size());
        for (final Object prop: props.keySet()) {
            final String propString = prop.toString();
            result.put(propString, props.getProperty(propString));
        }
        return result;
    }

    /**
     * Simple getter.
     * @return the value of "SESSION_SPECIFIC_ATOMIC_TyPES"
     */
    public List<String> getAtomicTypes() {
        String prop = this.properties.getProperty(SESSION_SPECIFIC_ATOMIC_TYPES);
        prop = this.replaceTypeAliases(prop);
        return readAndSplitList(prop);
    }

    /**
     * Simple getter.
     * @return value of "SYSTEM_DEFAULT_OUTPUT_PATH"
     */
    public String getDefaultOutputPath() {
        return (String) this.properties.get(SYSTEM_DEFAULT_OUTPUT_PATH);
    }

    /**
     * Returns the variable for the GNU C compiler executable file.
     *
     * @return the GNU C compiler executable file
     */
    public String getGccExecutable() {
        return this.properties.getProperty(GCC_BIN);
    }

    /**
     * Simple getter.
     *
     * @return String representation of the isabelle executable
     * @throws ExternalSoftwareUnavailableException if isabelle is unavailable
     */
    public String getIsabelleExecutable() throws ExternalSoftwareUnavailableException {
        if (!this.isabelleAvailable) {
            throw new ExternalSoftwareUnavailableException();
        }
        final Object value = this.properties.get(ISABELLE_BIN);
        return value != null ? value.toString() : StringUtils.EMPTY;
    }

    /**
     * Retrieves the path to $ISABELLE_HOME.
     *
     * @return the path
     * @throws ExternalSoftwareUnavailableException if Isabelle is unavailable
     */
    public String getIsabelleHome() throws ExternalSoftwareUnavailableException {
        if (!this.isabelleAvailable) {
            throw new ExternalSoftwareUnavailableException();
        }
        if (this.isabelleHome == null) {
            try {
                this.isabelleHome = this.computeIsabelleHome();
            } catch (final IOException e) {
                e.printStackTrace();
            } catch (final InterruptedException e) {
                e.printStackTrace();
            } catch (final ExternalSoftwareUnavailableException e) {
                e.printStackTrace();
            }
        }
        return this.isabelleHome;
    }

    /**
     * Retrieves the Isabelle session directory.
     *
     * @return the directory
     * @throws ExternalSoftwareUnavailableException if Isabelle is unavailable
     */
    public String getIsabelleSessionDir() throws ExternalSoftwareUnavailableException {
        if (!this.isabelleAvailable) {
            throw new ExternalSoftwareUnavailableException();
        }
        if (this.isabelleSessionDir == null) {
            try {
                this.isabelleSessionDir = this.computeIsabelleSessionDir();
            } catch (final IOException e) {
                e.printStackTrace();
            } catch (final InterruptedException e) {
                e.printStackTrace();
            } catch (final ExternalSoftwareUnavailableException e) {
                e.printStackTrace();
            }
        }
        // This is weird, but scala-isabelle expects .isabelle/, not
        // .isabelle/Isabelle202x.
        final File file = SystemUtils.file(this.isabelleSessionDir);
        this.isabelleSessionDir = file.getParentFile().getAbsolutePath();
        return this.isabelleSessionDir;
    }

    /**
     * Returns the configured Isabelle tactics.
     *
     * @return the configured Isabelle tactics
     */
    public List<String> getIsabelleTactics() {
        return readAndSplitList(this.properties.getProperty(ISABELLE_TACTICS));
    }

    /**
     * Returns the path to Isabelle's root file.
     *
     * @return Path to Isabelle's root file
     */
    public String getPathToRootFile() {
        return this.properties.getProperty(ROOT_FILE_PATH);
    }

    /**
     * Retrieves the component aliases.
     * @return the component aliases
     */
    public Map<String, String> getComponentAliases() {
        final List<String> pairStrings =
                readAndSplitList(this.properties.getProperty(COMPONENT_ALIASES));
        final Map<String, String> toReturn = Maps.newHashMapWithExpectedSize(pairStrings.size());
        for (final String pairString: pairStrings) {
            final String[] elements = pairString.split(PAIR_SEPARATOR);
            toReturn.put(elements[0], elements[1]);
        }
        return toReturn;
    }

    /**
     * Retrieves the SWI-Prolog home directory.
     *
     * @return the directory
     * @throws ExternalSoftwareUnavailableException if <code>swipl</code> (Prolog) is unavailable
     */
    public String getSwiplHome() throws ExternalSoftwareUnavailableException {
        if (!this.swiplAvailable) {
            throw new ExternalSoftwareUnavailableException();
        }
        if (this.swiplHome == null) {
            try {
                final String output =
                        getCommandOutput(this.properties.getProperty(SWIPL_BIN),
                                         DUMP_RUNTIME_VARIABLES);
                final String[] lines = output.split(System.lineSeparator());
                String value = StringUtils.EMPTY;
                for (final String line: lines) {
                    if (line.startsWith(PLBASE)) {
                        value = line;
                    }
                }
                final String path = value.split(KEY_VALUE_SEPARATOR)[1];
                this.swiplHome = path.substring(1, path.length() - 2);
                if (!this.swiplHome.endsWith(File.separator)) {
                    this.swiplHome = this.swiplHome + File.separator;
                }
            } catch (final IOException e) {
                e.printStackTrace();
            } catch (final InterruptedException e) {
                e.printStackTrace();
            }
        }
        return this.swiplHome;
    }

    /**
     * Retrieves the SWI-Prolog library directory via "<code>swipl --dump-runtime-variables</code>".
     * TODO: Disentangle spaghetti code.
     *
     * @return the directory
     * @throws ExternalSoftwareUnavailableException if Prolog is unavailable
     */
    public String getSwiplLib() throws ExternalSoftwareUnavailableException {
        if (!this.swiplAvailable) {
            throw new ExternalSoftwareUnavailableException();
        }
        if (this.swiplLib == null) {
            try {
                final String output =
                        getCommandOutput(this.properties.getProperty(SWIPL_BIN),
                                         DUMP_RUNTIME_VARIABLES);
                final String[] lines = output.split(System.lineSeparator());
                String value = StringUtils.EMPTY;
                String path = StringUtils.EMPTY;
                for (final String line: lines) {
                    if (line.startsWith(PLLIBDIR)) {
                        value = line;
                        path = value.split(KEY_VALUE_SEPARATOR)[1];
                    }
                }
                if (value.isEmpty()) {
                    for (final String line: lines) {
                        if (line.startsWith(PLARCH)) {
                            value = line;
                        }
                    }
                    if (value.isEmpty()) {
                        LOGGER.error("$" + PLARCH + " is undefined as well.");
                        throw new ExternalSoftwareUnavailableException();
                    } else {
                        String tmp = value.split(KEY_VALUE_SEPARATOR)[1];
                        tmp = tmp.substring(1, tmp.length() - 2);
                        path = this.swiplHome + "lib" + File.separator + tmp;
                    }
                } else {
                    path = path.substring(1, path.length() - 2);
                }
                while (path.contains(File.separator + File.separator)) {
                    path = path.replace(File.separator + File.separator, File.separator);
                }
                if (!path.endsWith(File.separator)) {
                    path = path + File.separator;
                }
                this.swiplLib = path;
            } catch (final IOException | InterruptedException e) {
                e.printStackTrace();
            }
        }
        return this.swiplLib;
    }

    /**
     * Returns the list of type synonyms defined in "SESSION_SPECIFIC_TYPE_SYNONYMS".
     *
     * @return the list
     * @throws IllegalArgumentException if the settings option is malformed
     */
    public List<Pair<String, String>> getTypeSynonyms() throws IllegalArgumentException {
        final List<Pair<String, String>> res = new LinkedList<Pair<String, String>>();
        String prop = this.properties.getProperty(SESSION_SPECIFIC_TYPE_SYNONYMS);
        prop = this.replaceTypeAliases(prop);
        final List<String> typeSynonyms = readAndSplitList(prop);
        for (final String synonym: typeSynonyms) {
            final String synonymCopy = this.replaceTypeAliases(synonym);
            final String[] splits = synonymCopy.split(PAIR_SEPARATOR);
            if (splits.length != 2) {
                throw new IllegalArgumentException();
            }
            res.add(new Pair<String, String>(splits[0], splits[1]));
        }
        return res;
    }

    /**
     * Simple getter.
     * @return true iff Isabelle is available
     */
    public boolean hasIsabelle() {
        return this.isabelleAvailable;
    }

    /**
     * Simple getter.
     * @return true iff JPL is available
     */
    public boolean hasJpl() {
        return this.jplAvailable;
    }

    /**
     * Simple getter.
     * @return true iff "ISABELLE_PATH_TO_ROOT_FILE" is specified
     */
    public boolean hasPathToRootFile() {
        return this.properties.containsKey(ROOT_FILE_PATH);
    }

    /**
     * Simple getter.
     * @return true iff "SESSION_SPECIFIC_TYPE_ALIASES" is specified
     */
    private boolean hasTypeAliases() {
        return this.properties.containsKey(SESSION_SPECIFIC_TYPE_ALIASES);
    }

    /**
     * Attempts to open settings file via the variable <code>xdg-open</code>, "SYSTEM_TEXT_EDITOR"
     * and $EDITOR.
     * @throws ExternalSoftwareUnavailableException if no editor is found
     */
    public void openConfigFileForEditing() throws ExternalSoftwareUnavailableException {
        ProcessUtils.start(XDG_OPEN, this.configFile);
        final String editorExecutable;
        if (this.properties.containsKey(SYSTEM_EDITOR)
                && !this.properties.getProperty(SYSTEM_EDITOR).isEmpty()) {
            editorExecutable = this.properties.getProperty(SYSTEM_EDITOR);
        } else if (System.getenv().containsKey(EDITOR)
                && !System.getenv().get(EDITOR).isEmpty()) {
            editorExecutable = System.getenv().get(EDITOR);
        } else {
            editorExecutable = StringUtils.EMPTY;
            throw new ExternalSoftwareUnavailableException();
        }
        ProcessUtils.start(editorExecutable, this.configFile);
    }

    private static List<String> readAndSplitList(final String list) {
        final String[] splits = list.split(LIST_SEPARATOR);
        final List<String> result = new LinkedList<String>();
        for (int i = 0; i < splits.length; i++) {
            result.add(splits[i]);
        }
        return result;
    }

    /**
     * Reads the settings-file supplied to ViRAGe.
     *
     * @param overwriteIfNecessary true if the existing settings file shall be
     *      overwritten by a fresh one
     * @throws IOException if reading the file is impossible
     * @throws InvalidConfigVersionException if the settings file is out of date
     */
    public void readConfigFile(final boolean overwriteIfNecessary) throws IOException {
        this.properties = new Properties();
        final File virageDir = SystemUtils.file(virageFolderPath);
        this.configFile = SystemUtils.file(configPath);
        if (!this.configFile.exists()) {
            if (!virageDir.exists()) {
                Files.createDirectory(virageDir.toPath());
            }
            Files.createFile(this.configFile.toPath());
            this.copyConfigToExpectedPath();
        }
        final Properties proposedProperties = new Properties();
        try (InputStream fis = java.nio.file.Files.newInputStream(this.configFile.toPath())) {
            proposedProperties.load(fis);
        } catch (IOException e) {
            e.printStackTrace();
        }
        final Pair<Boolean, List<String>> configCompatibility = this.checkConfigCompatibility();
        if (configCompatibility.getFirstValue()) {
            this.properties = proposedProperties;
        } else {
            if (overwriteIfNecessary) {
                this.copyConfigToExpectedPath();
            } else {
                throw new InvalidConfigVersionException("The settings file at " + configPath
                        + " is missing the following keys: "
                        + StringUtils.printCollection(configCompatibility.getSecondValue()));
            }
        }
        try (InputStream fis = java.nio.file.Files.newInputStream(this.configFile.toPath())) {
            this.properties.load(fis);
        } catch (IOException e) {
            e.printStackTrace();
        }
    }

    private String replaceTypeAliases(final String s) {
        String copyOfs = s;
        if (!this.hasTypeAliases()) {
            return copyOfs;
        }
        final List<String> replacements =
                readAndSplitList(this.properties.getProperty(SESSION_SPECIFIC_TYPE_ALIASES));
        final Map<String, String> replMap = Maps.newHashMapWithExpectedSize(replacements.size());
        for (final String repl: replacements) {
            final String[] parts = repl.split(PAIR_SEPARATOR);
            if (parts.length != 2) {
                throw new IllegalArgumentException();
            }
            replMap.put(parts[0], parts[1]);
        }
        for (final Map.Entry<String, String> aliasEntry: replMap.entrySet()) {
            copyOfs = copyOfs.replaceAll(aliasEntry.getKey(), aliasEntry.getValue());
        }
        return copyOfs;
    }

    private void updateValue(final String name, final String newValue) {
        final Parameters params = new Parameters();
        final FileBasedConfigurationBuilder<FileBasedConfiguration> builder =
                new FileBasedConfigurationBuilder<FileBasedConfiguration>(
                PropertiesConfiguration.class)
                .configure(params.properties().setFileName(configPath));
        final Configuration config;
        try {
            config = builder.getConfiguration();
            config.setProperty(name, newValue);
            config.setProperty(TIMESTAMP, SystemUtils.getCurrentTime());
            builder.save();
        } catch (final ConfigurationException e) {
            LOGGER.error("Updating \"" + name + "\" failed.");
        }
    }

    /**
     * Updates value of "SWI_PROLOG_LIBRARIES_PATH".
     * @param newValue the new value
     */
    public void updateValueForSwiPrologLibrariesPath(final String newValue) {
        this.updateValue(SWI_PROLOG_LIBRARIES_PATH, newValue);
    }

    /**
     * Updates value of "SWI_PROLOG_LIBSWIPL_PATH".
     * @param newValue the new value
     */
    public void updateValueForLibswiplPath(final String newValue) {
        this.updateValue(SWI_PROLOG_LIBSWIPL_PATH, newValue);
    }
}
