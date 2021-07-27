package com.fr2501.virage.core;

import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.StringWriter;
import java.nio.charset.StandardCharsets;
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

import com.fr2501.util.Pair;
import com.fr2501.util.ProcessUtils;
import com.fr2501.util.SimpleFileReader;
import com.fr2501.util.SimpleFileWriter;
import com.fr2501.util.StringUtils;
import com.fr2501.virage.types.ExternalSoftwareUnavailableException;
import com.fr2501.virage.types.InvalidConfigVersionException;

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
     * Name of the option containing the Isabelle binary.
     */
    private static final String ISABELLE_BIN = "ISABELLE_EXECUTABLE";
    /**
     * Name of the option containing the SWI-Prolog binary.
     */
    private static final String SWIPL_BIN = "SWI_PROLOG_EXECUTABLE";

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
        virageFolderPath = System.getProperty("user.home") + File.separator + ".virage"
                + File.separator;
        configPath = virageFolderPath + "settings";

        // This is only to ensure unit-tests are working.
        try {
            this.readConfigFile(false);
        } catch (final IOException e) {
            // Nothing to be done
        }
    }

    /**
     * Simple getter.
     * @return the config path
     */
    public static String getConfigPath() {
        virageFolderPath = System.getProperty("user.home") + File.separator + ".virage"
                + File.separator;
        configPath = virageFolderPath + "settings";

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
            res += "Isabelle: \t\t"
                    + ProcessUtils.runTerminatingProcess(this.getIsabelleExecutable() + " version")
                    .getFirstValue();
            res += "Scala (via Isabelle): " + ProcessUtils
                    .runTerminatingProcess(this.getIsabelleExecutable() + " scalac -version")
            .getFirstValue();
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
            res += "SWI-Prolog: \t\t" + ProcessUtils
                    .runTerminatingProcess(this.properties.get(SWIPL_BIN) + " --version")
            .getFirstValue();
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
        final InputStream input = new FileInputStream(this.configFile);
        oldProperties.load(input);

        final Properties newProperties = new Properties();
        final InputStream newPropertiesStream = this.getClass().getClassLoader()
                .getResourceAsStream("settings");
        newProperties.load(newPropertiesStream);

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
        final String output = ProcessUtils
                .runTerminatingProcess(this.getIsabelleExecutable() + " getenv ISABELLE_HOME")
                .getFirstValue();

        return output.split("=")[1].trim();
    }

    private String computeIsabelleSessionDir()
            throws IOException, InterruptedException, ExternalSoftwareUnavailableException {
        final String output = ProcessUtils
                .runTerminatingProcess(this.getIsabelleExecutable() + " getenv ISABELLE_HOME_USER")
                .getFirstValue();

        return output.split("=")[1].trim();
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
            oldPropertiesFile.createNewFile();
        }

        writer.writeToFile(oldPropertiesFile.getAbsolutePath(), reader.readFile(this.configFile));

        final Properties oldProperties = new Properties();
        oldProperties.load(new FileInputStream(oldPropertiesFile));

        final InputStream configFromResourcesStream = this.getClass().getClassLoader()
                .getResourceAsStream("settings");
        final StringWriter stringWriter = new StringWriter();
        IOUtils.copy(configFromResourcesStream, stringWriter, StandardCharsets.UTF_8);

        writer.writeToFile(this.configFile.getAbsolutePath(), stringWriter.toString());

        final Properties newProperties = new Properties();
        newProperties.load(new FileInputStream(this.configFile));

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
        String prop = this.properties.getProperty("SESSION_SPECIFIC_ASSUMPTIONS");
        prop = this.replaceTypeAliases(prop);

        return this.readAndSplitList(prop);
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

        return this.readAndSplitList(prop);
    }

    /**
     * Simple getter.
     * @return value of "SYSTEM_DEFAULT_OUTPUT_PATH"
     */
    public String getDefaultOutputPath() {
        final String defaultPath = "./target/generated-sources/";

        final String configValue = (String) this.properties
                .getOrDefault("SYSTEM_DEFAULT_OUTPUT_PATH", "./target/generated-sources/");

        if (configValue.isEmpty()) {
            return defaultPath;
        } else {
            return configValue;
        }
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
        return this.readAndSplitList(this.properties.getProperty("ISABELLE_TACTICS"));
    }

    public String getPathToRootFile() {
        return this.properties.getProperty("ISABELLE_PATH_TO_ROOT_FILE");
    }

    public String getSessionName() {
        return this.properties.getProperty("ISABELLE_SESSION_NAME");
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
                final String output = ProcessUtils.runTerminatingProcess(
                        this.properties.getProperty(SWIPL_BIN) + " --dump-runtime-variables")
                        .getFirstValue();
                final String[] lines = output.split(System.lineSeparator());
                String value = "";
                for (final String line : lines) {
                    if (line.startsWith("PLBASE")) {
                        value = line;
                    }
                }

                final String path = value.split("=")[1];

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
                final String output = ProcessUtils.runTerminatingProcess(
                        this.properties.getProperty(SWIPL_BIN) + " --dump-runtime-variables")
                        .getFirstValue();
                final String[] lines = output.split(System.lineSeparator());
                String value = "";
                String path = "";
                for (final String line : lines) {
                    if (line.startsWith("PLLIBDIR")) {
                        value = line;
                        path = value.split("=")[1];
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
                        String tmp = value.split("=")[1];
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
        final List<String> typeSynonyms = this.readAndSplitList(prop);

        for (final String synonym : typeSynonyms) {
            final String synonymCopy = this.replaceTypeAliases(synonym);

            final String[] splits = synonymCopy.split("->");

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
        return this.properties.containsKey("ISABELLE_PATH_TO_ROOT_FILE");
    }

    /**
     * Simple getter.
     * @return true iff "ISABELLE_SESSION_NAME" is specified
     */
    public boolean hasSessionName() {
        return this.properties.containsKey("ISABELLE_SESSION_NAME");
    }

    /**
     * Simple getter.
     * @return true iff "SESSION_SPECIFIC_TYPE_ALIASES" is specified
     */
    private boolean hasTypeAliases() {
        return this.properties.containsKey("SESSION_SPECIFIC_TYPE_ALIASES");
    }

    /**
     * Attempts to open settings file via xdg-open, "SYSTEM_TEXT_EDITOR" and $EDITOR.
     * @throws ExternalSoftwareUnavailableException if no editor is found
     */
    public void openConfigFileForEditing() throws ExternalSoftwareUnavailableException {
        String editorExecutable = "";

        try {
            final Process process = new ProcessBuilder("xdg-open",
                    this.configFile.getAbsolutePath()).directory(null).start();
            process.waitFor();
            return;
        } catch (final IOException e) {
            e.printStackTrace();
        } catch (final InterruptedException e) {
            e.printStackTrace();
        }

        if (this.properties.containsKey("SYSTEM_TEXT_EDITOR")
                && !this.properties.getProperty("SYSTEM_TEXT_EDITOR").toString().isEmpty()) {
            editorExecutable = this.properties.getProperty("SYSTEM_TEXT_EDITOR");
        } else if (System.getenv().containsKey("EDITOR")
                && !System.getenv().get("EDITOR").isEmpty()) {
            editorExecutable = System.getenv().get("EDITOR");
        } else {
            throw new ExternalSoftwareUnavailableException();
        }

        try {
            final Process process = new ProcessBuilder(editorExecutable,
                    this.configFile.getAbsolutePath()).directory(null).start();
            process.waitFor();
        } catch (final InterruptedException e) {
            e.printStackTrace();
        } catch (final IOException e) {
            e.printStackTrace();
        }
    }

    private List<String> readAndSplitList(final String list) {
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
            virageDir.mkdir();
            this.configFile.createNewFile();
            this.copyConfigToExpectedPath();
        }

        final Properties proposedProperties = new Properties();

        final InputStream input = new FileInputStream(this.configFile);

        proposedProperties.load(input);

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

        this.properties.load(new FileInputStream(this.configFile));
    }

    private String replaceTypeAliases(final String s) {
        String copyOfs = s;

        if (!this.hasTypeAliases()) {
            return copyOfs;
        }

        final List<String> replacements = this
                .readAndSplitList(this.properties.getProperty("SESSION_SPECIFIC_TYPE_ALIASES"));

        final Map<String, String> replMap = new HashMap<String, String>();

        for (final String repl : replacements) {
            final String[] parts = repl.split("->");
            if (parts.length != 2) {
                throw new IllegalArgumentException();
            }

            replMap.put(parts[0], parts[1]);
        }

        for (final String alias : replMap.keySet()) {
            copyOfs = copyOfs.replaceAll(alias, replMap.get(alias));
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
