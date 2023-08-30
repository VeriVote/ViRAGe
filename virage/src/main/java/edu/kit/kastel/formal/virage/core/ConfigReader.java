package edu.kit.kastel.formal.virage.core;

import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.StringWriter;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.util.HashMap;
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

import edu.kit.kastel.formal.util.Pair;
import edu.kit.kastel.formal.util.ProcessUtils;
import edu.kit.kastel.formal.util.SimpleFileReader;
import edu.kit.kastel.formal.util.SimpleFileWriter;
import edu.kit.kastel.formal.util.StringUtils;
import edu.kit.kastel.formal.util.SystemUtils;
import edu.kit.kastel.formal.virage.types.ExternalSoftwareUnavailableException;
import edu.kit.kastel.formal.virage.types.InvalidConfigVersionException;

/**
 * A class to interact with a ViRAGe config file.
 *
 * @author VeriVote
 */
public final class ConfigReader {
    /**
     * THe logger.
     */
    private static final Logger LOGGER = LogManager.getRootLogger();

    /**
     * Character used to separate lists in the settings file.
     */
    private static final String LIST_SEPARATOR = ";";

    /**
     * The separator between keys and values.
     */
    private static final String KEY_VALUE_SEPARATOR = "=";

    /**
     * The separator for mappings.
     */
    private static final String PAIR_SEPARATOR = "->";

    /**
     * The default virage folder name.
     */
    private static final String VIRAGE_FOLDER = ".virage";

    /**
     * Name of the settings file.
     */
    private static final String SETTINGS = "settings";

    /**
     * The user.home system property.
     */
    private static final String USER_HOME = "user.home";

    /**
     * Name of the option containing the Isabelle binary.
     */
    private static final String ISABELLE_BIN = "ISABELLE_EXECUTABLE";
    /**
     * Name of the option containing the SWI-Prolog binary.
     */
    private static final String SWIPL_BIN = "SWI_PROLOG_EXECUTABLE";

    /**
     * Name of the option containing the GCC binary.
     */
    private static final String GCC_BIN = "GCC_EXECUTABLE";

    /**
     * Name of the option containing session specific component aliases.
     */
    private static final String COMPONENT_ALIASES = "SESSION_SPECIFIC_COMPONENT_ALIASES";

    /**
     * Name of the option containing the path to a ROOT file.
     */
    private static final String ISABELLE_PATH_TO_ROOT_FILE = "ISABELLE_PATH_TO_ROOT_FILE";

    /**
     * Name of the option containing the system text editor.
     */
    private static final String SYSTEM_TEXT_EDITOR = "SYSTEM_TEXT_EDITOR";

    /**
     * Name of the option containing type aliases.
     */
    private static final String SESSION_SPECIFIC_TYPE_ALIASES = "SESSION_SPECIFIC_TYPE_ALIASES";

    /**
     * The environment variable containing the default text editor.
     */
    private static final String EDITOR = "EDITOR";

    /**
     * Name of the option containing session specific assumptions.
     */
    private static final String SESSION_SPECIFIC_ASSUMPTIONS = "SESSION_SPECIFIC_ASSUMPTIONS";

    /**
     * SWI-Prolog option to dump runtime variables.
     */
    private static final String DUMP_RUNTIME_VARIABLES = "--dump-runtime-variables";

    /**
     * THe xdg-open command. Maybe only makes real sense for unix systems, but well.
     */
    private static final String XDG_OPEN = "xdg-open";

    /**
     * Singleton instance.
     */
    private static ConfigReader instance;

    /**
     * Path to the settings file.
     */
    private static String configPath;
    /**
     * Path to the .virage-folder.
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
        virageFolderPath = System.getProperty(USER_HOME) + File.separator + VIRAGE_FOLDER
                + File.separator;
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
     * @return the config path
     */
    public static String getConfigPath() {
        virageFolderPath = System.getProperty(USER_HOME) + File.separator + VIRAGE_FOLDER
                + File.separator;
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
        final String none = "<NONE>" + '\n';
        final String proc = command + " " + option;
        final String output = ProcessUtils.runTerminatingProcess(proc).getFirstValue();
        return output.isEmpty() ? none : output;
    }

    /**
     * Checks whether all external software is available and prints the version numbers of said
     * software.
     * @return string representation of all software and versions
     */
    public String checkAvailabilityAndGetVersions() {
        String res = "External dependency versions:\n\n";

        // JAVA
        res += "Java: \t\t" + System.getProperty("java.version") + System.lineSeparator();

        // ISABELLE
        try {
            final String isaExec = this.getIsabelleExecutable();
            res += "Isabelle: \t\t" + getCommandOutput(isaExec, "version");
            res += "Scala (via Isabelle): " + getCommandOutput(isaExec + " scalac", "-version");
        } catch (final IOException e) {
            res += "Isabelle: \t\tNOT FOUND\n";
            this.isabelleAvailable = false;
        } catch (final InterruptedException e) {
            e.printStackTrace();
        } catch (final ExternalSoftwareUnavailableException e) {
            e.printStackTrace();
        }

        // SWIPL
        try {
            res += "SWI-Prolog: \t\t"
                    + getCommandOutput((String)this.properties.get(SWIPL_BIN), "--version");
        } catch (final IOException e) {
            System.out.println("SWI-Prolog: NOT FOUND\n");
            this.swiplAvailable = false;
            this.jplAvailable = false;
        } catch (final InterruptedException e) {
            e.printStackTrace();
        }

        try {
            this.getSwiplHome();
            this.getSwiplLib();
        } catch (final ExternalSoftwareUnavailableException e) {
            this.jplAvailable = false;
            this.swiplAvailable = false;
        }

        res += "JPL: \t\t\t" + JPL.version_string();

        return res;
    }

    private Pair<Boolean, List<String>> checkConfigCompatibility() throws IOException {
        final Properties oldProperties = new Properties();
        try (FileInputStream fis = new FileInputStream(this.configFile)) {
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

        outer: for (final Object newKey : newProperties.keySet()) {
            for (final Object oldKey : oldProperties.keySet()) {
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
                getCommandOutput(this.getIsabelleExecutable(), "getenv ISABELLE_HOME");

        return output.split(KEY_VALUE_SEPARATOR)[1].trim();
    }

    private String computeIsabelleSessionDir()
            throws IOException, InterruptedException, ExternalSoftwareUnavailableException {
        final String output =
                getCommandOutput(this.getIsabelleExecutable(), "getenv ISABELLE_HOME_USER");

        return output.split(KEY_VALUE_SEPARATOR)[1].trim();
    }

    /**
     * Copies settings from src/resources to $USER_HOME/.virage.
     * @throws IOException if io fails
     */
    public void copyConfigToExpectedPath() throws IOException {
        final SimpleFileReader reader = new SimpleFileReader();
        final SimpleFileWriter writer = new SimpleFileWriter();

        final File oldPropertiesFile = new File(virageFolderPath + "old_settings");
        if (!oldPropertiesFile.exists()) {
            Files.createFile(oldPropertiesFile.toPath());
        }

        writer.writeToFile(oldPropertiesFile.getAbsolutePath(), reader.readFile(this.configFile));

        final Properties oldProperties = new Properties();
        try (FileInputStream fis = new FileInputStream(oldPropertiesFile)) {
            oldProperties.load(fis);
        } catch (IOException e) {
            e.printStackTrace();
        }

        final InputStream configFromResourcesStream = this.getClass().getClassLoader()
                .getResourceAsStream(SETTINGS);
        final StringWriter stringWriter = new StringWriter();
        IOUtils.copy(configFromResourcesStream, stringWriter, StandardCharsets.UTF_8);

        writer.writeToFile(this.configFile.getAbsolutePath(), stringWriter.toString());

        final Properties newProperties = new Properties();
        try (FileInputStream fis = new FileInputStream(this.configFile)) {
            newProperties.load(fis);
        }

        for (final Object o : oldProperties.keySet()) {
            if (o.toString().equals("VIRAGE_CONFIG_VERSION")) {
                continue;
            }

            if (newProperties.keySet().contains(o)) {
                this.updateValue(o.toString(), oldProperties.getProperty(o.toString()));
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
        final Map<String, String> result = new HashMap<String, String>();

        for (final Object prop : this.properties.keySet()) {
            result.put(prop.toString(), this.properties.getProperty(prop.toString()));
        }

        return result;
    }

    /**
     * Simple getter.
     * @return the value of "SESSION_SPECIFIC_ATOMIC_TyPES"
     */
    public List<String> getAtomicTypes() {
        String prop = this.properties.getProperty("SESSION_SPECIFIC_ATOMIC_TYPES");
        prop = this.replaceTypeAliases(prop);

        return readAndSplitList(prop);
    }

    /**
     * Simple getter.
     * @return value of "SYSTEM_DEFAULT_OUTPUT_PATH"
     */
    public String getDefaultOutputPath() {
        final String configValue = (String) this.properties
                .get("SYSTEM_DEFAULT_OUTPUT_PATH");

        return configValue;
    }

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

        return this.properties.get(ISABELLE_BIN).toString();
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
        final File file = new File(this.isabelleSessionDir);
        this.isabelleSessionDir = file.getParentFile().getAbsolutePath();

        return this.isabelleSessionDir;
    }

    public List<String> getIsabelleTactics() {
        return readAndSplitList(this.properties.getProperty("ISABELLE_TACTICS"));
    }

    public String getPathToRootFile() {
        return this.properties.getProperty(ISABELLE_PATH_TO_ROOT_FILE);
    }

    /**
     * Retrieves the component aliases.
     * @return the component aliases
     */
    public Map<String, String> getComponentAliases() {
        final Map<String, String> toReturn = new HashMap<String, String>();
        final List<String> pairStrings =
                readAndSplitList(this.properties.getProperty(COMPONENT_ALIASES));

        for(final String pairString: pairStrings) {
            final String[] elements = pairString.split(PAIR_SEPARATOR);
            toReturn.put(elements[0], elements[1]);
        }

        return toReturn;
    }

    /**
     * Retrieves the SWI-Prolog home directory.
     *
     * @return the directory
     * @throws ExternalSoftwareUnavailableException if swipl is unavailable
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
                String value = "";
                for (final String line : lines) {
                    if (line.startsWith("PLBASE")) {
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

    // TODO: De-spaghettize
    /**
     * Retrieves the SWI-Prolog library directory via "swipl --dump-runtime-variables".
     *
     * @return the directory
     * @throws ExternalSoftwareUnavailableException if swipl is unavailable
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
                String value = "";
                String path = "";
                for (final String line : lines) {
                    if (line.startsWith("PLLIBDIR")) {
                        value = line;
                        path = value.split(KEY_VALUE_SEPARATOR)[1];
                    }
                }

                if (value.isEmpty()) {

                    for (final String line : lines) {
                        if (line.startsWith("PLARCH")) {
                            value = line;
                        }
                    }

                    if (value.isEmpty()) {
                        LOGGER.error("$PLARCH is undefined as well.");
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
            } catch (final IOException e) {
                e.printStackTrace();
            } catch (final InterruptedException e) {
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

        String prop = this.properties.getProperty("SESSION_SPECIFIC_TYPE_SYNONYMS");
        prop = this.replaceTypeAliases(prop);
        final List<String> typeSynonyms = readAndSplitList(prop);

        for (final String synonym : typeSynonyms) {
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
        return this.properties.containsKey(ISABELLE_PATH_TO_ROOT_FILE);
    }

    /**
     * Simple getter.
     * @return true iff "SESSION_SPECIFIC_TYPE_ALIASES" is specified
     */
    private boolean hasTypeAliases() {
        return this.properties.containsKey(SESSION_SPECIFIC_TYPE_ALIASES);
    }

    /**
     * Attempts to open settings file via xdg-open, "SYSTEM_TEXT_EDITOR" and $EDITOR.
     * @throws ExternalSoftwareUnavailableException if no editor is found
     */
    public void openConfigFileForEditing() throws ExternalSoftwareUnavailableException {
        String editorExecutable = "";

        try {
            final Process process = new ProcessBuilder(StringUtils.stripAndEscape(XDG_OPEN),
                    this.configFile.getAbsolutePath()).directory(null).start();
            process.waitFor();
            return;
        } catch (final IOException e) {
            e.printStackTrace();
        } catch (final InterruptedException e) {
            e.printStackTrace();
        }

        if (this.properties.containsKey(SYSTEM_TEXT_EDITOR)
                && !this.properties.getProperty(SYSTEM_TEXT_EDITOR).toString().isEmpty()) {
            editorExecutable = this.properties.getProperty(SYSTEM_TEXT_EDITOR);
        } else if (System.getenv().containsKey(EDITOR)
                && !System.getenv().get(EDITOR).isEmpty()) {
            editorExecutable = System.getenv().get(EDITOR);
        } else {
            throw new ExternalSoftwareUnavailableException();
        }
        try {
            final Process process =
                    new ProcessBuilder(StringUtils.stripAndEscape(editorExecutable),
                                       this.configFile.getAbsolutePath())
                    .directory(null).start();
            process.waitFor();
        } catch (final InterruptedException e) {
            e.printStackTrace();
        } catch (final IOException e) {
            e.printStackTrace();
        }
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
     * @throws InvalidConfigVersionException if the settings file is outdated
     */
    public void readConfigFile(final boolean overwriteIfNecessary) throws IOException {
        this.properties = new Properties();

        final File virageDir = new File(virageFolderPath);
        this.configFile = new File(configPath);
        if (!this.configFile.exists()) {
            Files.createDirectory(virageDir.toPath());
            Files.createFile(this.configFile.toPath());
            this.copyConfigToExpectedPath();
        }

        final Properties proposedProperties = new Properties();

        try (FileInputStream fis = new FileInputStream(this.configFile)) {
            proposedProperties.load(fis);
        } catch (IOException e) {
            e.printStackTrace();
        }

        final var configCompatibility = this.checkConfigCompatibility();

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

        try (FileInputStream fis = new FileInputStream(this.configFile)) {
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

        final Map<String, String> replMap = new HashMap<String, String>();

        for (final String repl : replacements) {
            final String[] parts = repl.split(PAIR_SEPARATOR);
            if (parts.length != 2) {
                throw new IllegalArgumentException();
            }

            replMap.put(parts[0], parts[1]);
        }

        for (final Map.Entry<String, String> aliasEntry : replMap.entrySet()) {
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
            config.setProperty("TIMESTAMP", SystemUtils.getTime());
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
        this.updateValue("SWI_PROLOG_LIBRARIES_PATH", newValue);
    }

    /**
     * Updates value of "SWI_PROLOG_LIBSWIPL_PATH".
     * @param newValue the new value
     */
    public void updateValueForLibswiplPath(final String newValue) {
        this.updateValue("SWI_PROLOG_LIBSWIPL_PATH", newValue);
    }
}
