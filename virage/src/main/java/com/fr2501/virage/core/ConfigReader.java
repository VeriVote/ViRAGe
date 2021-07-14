package com.fr2501.virage.core;

import com.fr2501.util.Pair;
import com.fr2501.util.ProcessUtils;
import com.fr2501.util.SimpleFileReader;
import com.fr2501.util.SimpleFileWriter;
import com.fr2501.virage.types.ExternalSoftwareUnavailableException;
import com.fr2501.virage.types.InvalidConfigVersionException;

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

/**
 * A class to interact with a ViRAGe config file.
 *
 */
public class ConfigReader {
    Logger logger = LogManager.getRootLogger();

    private static final String LIST_SEPARATOR = ";";

    private static final String ISABELLE_BIN = "ISABELLE_EXECUTABLE";
    private static final String SWIPL_BIN = "SWI_PROLOG_EXECUTABLE";

    private static String CONFIG_PATH;
    private static String VIRAGE_FOLDER_PATH;

    private boolean isabelleAvailable = true;
    private boolean swiplAvailable = true;
    private boolean jplAvailable = true;

    private String isabelleHome;
    private String swiplHome;
    private String swiplLib;
    private String isabelleSessionDir;

    private Properties properties;

    private static ConfigReader instance;

    private File configFile;

    private ConfigReader() {
        VIRAGE_FOLDER_PATH = System.getProperty("user.home") + File.separator + ".virage"
                + File.separator;
        CONFIG_PATH = VIRAGE_FOLDER_PATH + "settings";

        // This is only to ensure unit-tests are working.
        try {
            this.readConfigFile(false);
        } catch (Exception e) {
            // Nothing to be done
        }
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

    public static String getConfigPath() {
        VIRAGE_FOLDER_PATH = System.getProperty("user.home") + File.separator + ".virage"
                + File.separator;
        CONFIG_PATH = VIRAGE_FOLDER_PATH + "settings";

        return CONFIG_PATH;
    }

    /**
     * Reads the settings-file supplied to ViRAGe.
     * 
     * @throws IOException if reading the file is impossible
     */
    public void readConfigFile(boolean overwriteIfNecessary) throws IOException {
        this.properties = new Properties();

        File virageDir = new File(VIRAGE_FOLDER_PATH);
        this.configFile = new File(CONFIG_PATH);
        if (!this.configFile.exists()) {
            virageDir.mkdir();
            this.configFile.createNewFile();
            this.copyConfigToExpectedPath();
        }

        Properties proposedProperties = new Properties();

        InputStream input = new FileInputStream(this.configFile);

        proposedProperties.load(input);

        if (proposedProperties.containsKey("VIRAGE_CONFIG_VERSION") && proposedProperties
                .getProperty("VIRAGE_CONFIG_VERSION").equals(VirageCore.getVersion())) {
            this.properties = proposedProperties;
        } else {
            if (overwriteIfNecessary) {
                this.copyConfigToExpectedPath();
            } else {
                throw new InvalidConfigVersionException(
                        "Expected config version " + VirageCore.getVersion() + ", found "
                                + proposedProperties.getProperty("VIRAGE_CONFIG_VERSION") + ".");
            }
        }

        this.properties.load(new FileInputStream(this.configFile));
    }

    public void copyConfigToExpectedPath() throws IOException {
        SimpleFileReader reader = new SimpleFileReader();
        SimpleFileWriter writer = new SimpleFileWriter();

        File oldPropertiesFile = new File(VIRAGE_FOLDER_PATH + "old_settings");
        if (!oldPropertiesFile.exists()) {
            oldPropertiesFile.createNewFile();
        }

        writer.writeToFile(oldPropertiesFile.getAbsolutePath(), reader.readFile(this.configFile));

        Properties oldProperties = new Properties();
        oldProperties.load(new FileInputStream(oldPropertiesFile));

        InputStream configFromResourcesStream = this.getClass().getClassLoader()
                .getResourceAsStream("settings");
        StringWriter stringWriter = new StringWriter();
        IOUtils.copy(configFromResourcesStream, stringWriter, StandardCharsets.UTF_8);

        writer.writeToFile(this.configFile.getAbsolutePath(), stringWriter.toString());

        Properties newProperties = new Properties();
        newProperties.load(new FileInputStream(this.configFile));

        for (Object o : oldProperties.keySet()) {
            if (o.toString().equals("VIRAGE_CONFIG_VERSION")) {
                continue;
            }

            if (newProperties.keySet().contains(o)) {
                this.updateValue(o.toString(), oldProperties.getProperty(o.toString()));
            }
        }
    }

    public Map<String, String> getAllProperties() {
        Map<String, String> result = new HashMap<String, String>();

        for (Object prop : this.properties.keySet()) {
            result.put(prop.toString(), this.properties.getProperty(prop.toString()));
        }

        return result;
    }

    /**
     * Checks whether all external software is available and prints the version numbers of said
     * software.
     */
    public String checkAvailabilityAndGetVersions() {
        String res = "External dependency versions:\n\n";

        // JAVA
        res += "Java: \t\t" + System.getProperty("java.version") + "\n";

        // ISABELLE
        try {
            res += "Isabelle: \t\t"
                    + ProcessUtils.runTerminatingProcess(this.getIsabelleExecutable() + " version")
                            .getFirstValue();
            res += "Scala (via Isabelle): " + ProcessUtils
                    .runTerminatingProcess(this.getIsabelleExecutable() + " scalac -version")
                    .getFirstValue();
        } catch (IOException e) {
            res += ("Isabelle: \t\tNOT FOUND\n");
            this.isabelleAvailable = false;
        } catch (InterruptedException e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
        } catch (ExternalSoftwareUnavailableException e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
        }

        // SWIPL
        try {
            res += "SWI-Prolog: \t\t" + ProcessUtils
                    .runTerminatingProcess(this.properties.get(SWIPL_BIN) + " --version")
                    .getFirstValue();
        } catch (IOException e) {
            System.out.println("SWI-Prolog: NOT FOUND\n");
            this.swiplAvailable = false;
            this.jplAvailable = false;
        } catch (InterruptedException e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
        }

        try {
            this.getSwiplHome();
            this.getSwiplLib();
        } catch (ExternalSoftwareUnavailableException e) {
            this.jplAvailable = false;
            this.swiplAvailable = false;
        }

        res += ("JPL: \t\t\t" + JPL.version_string());

        return res;
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

    public boolean hasIsabelle() {
        return this.isabelleAvailable;
    }

    public List<String> getIsabelleTactics() {
        return this.readAndSplitList(this.properties.getProperty("ISABELLE_TACTICS"));
    }

    /**
     * Returns the list of type synonyms defined in "SESSION_SPECIFIC_TYPE_SYNONYMS".
     * 
     * @return the list
     */
    public List<Pair<String, String>> getTypeSynonyms() {
        List<Pair<String, String>> res = new LinkedList<Pair<String, String>>();

        String prop = this.properties.getProperty("SESSION_SPECIFIC_TYPE_SYNONYMS");
        prop = this.replaceTypeAliases(prop);
        List<String> typeSynonyms = this.readAndSplitList(prop);

        for (String synonym : typeSynonyms) {
            synonym = this.replaceTypeAliases(synonym);

            String[] splits = synonym.split("->");

            if (splits.length != 2) {
                throw new IllegalArgumentException();
            }

            res.add(new Pair<String, String>(splits[0], splits[1]));
        }

        return res;
    }

    public List<String> getAtomicTypes() {
        String prop = this.properties.getProperty("SESSION_SPECIFIC_ATOMIC_TYPES");
        prop = this.replaceTypeAliases(prop);

        return this.readAndSplitList(prop);
    }

    private List<String> readAndSplitList(String list) {
        String[] splits = list.split(LIST_SEPARATOR);

        List<String> result = new LinkedList<String>();
        for (int i = 0; i < splits.length; i++) {
            result.add(splits[i]);
        }

        return result;
    }

    public List<String> getAdditionalProperties() {
        String prop = this.properties.getProperty("SESSION_SPECIFIC_ASSUMPTIONS");
        prop = this.replaceTypeAliases(prop);

        return this.readAndSplitList(prop);
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
            } catch (IOException e) {
                // TODO Auto-generated catch block
                e.printStackTrace();
            } catch (InterruptedException e) {
                // TODO Auto-generated catch block
                e.printStackTrace();
            } catch (ExternalSoftwareUnavailableException e) {
                // TODO Auto-generated catch block
                e.printStackTrace();
            }
        }

        return this.isabelleHome;
    }

    private String computeIsabelleHome()
            throws IOException, InterruptedException, ExternalSoftwareUnavailableException {
        String output = ProcessUtils
                .runTerminatingProcess(this.getIsabelleExecutable() + " getenv ISABELLE_HOME")
                .getFirstValue();

        return (output.split("=")[1].trim());
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
            } catch (IOException e) {
                // TODO Auto-generated catch block
                e.printStackTrace();
            } catch (InterruptedException e) {
                // TODO Auto-generated catch block
                e.printStackTrace();
            } catch (ExternalSoftwareUnavailableException e) {
                // TODO Auto-generated catch block
                e.printStackTrace();
            }
        }

        // This is weird, but scala-isabelle expects .isabelle/, not
        // .isabelle/Isabelle202x.
        File file = new File(this.isabelleSessionDir);
        this.isabelleSessionDir = file.getParentFile().getAbsolutePath();

        return this.isabelleSessionDir;
    }

    private String computeIsabelleSessionDir()
            throws IOException, InterruptedException, ExternalSoftwareUnavailableException {
        String output = ProcessUtils
                .runTerminatingProcess(this.getIsabelleExecutable() + " getenv ISABELLE_HOME_USER")
                .getFirstValue();

        return (output.split("=")[1].trim());
    }

    public boolean hasPathToRootFile() {
        return this.properties.containsKey("ISABELLE_PATH_TO_ROOT_FILE");
    }

    public String getPathToRootFile() {
        return this.properties.getProperty("ISABELLE_PATH_TO_ROOT_FILE");
    }

    public boolean hasSessionName() {
        return this.properties.containsKey("ISABELLE_SESSION_NAME");
    }

    public String getSessionName() {
        return this.properties.getProperty("ISABELLE_SESSION_NAME");
    }

    public boolean hasJpl() {
        return this.jplAvailable;
    }

    private boolean hasTypeAliases() {
        return this.properties.containsKey("SESSION_SPECIFIC_TYPE_ALIASES");
    }

    private String replaceTypeAliases(String s) {
        if (!this.hasTypeAliases()) {
            return s;
        }

        List<String> replacements = this
                .readAndSplitList(this.properties.getProperty("SESSION_SPECIFIC_TYPE_ALIASES"));

        Map<String, String> replMap = new HashMap<String, String>();

        for (String repl : replacements) {
            String[] parts = repl.split("->");
            if (parts.length != 2) {
                throw new IllegalArgumentException();
            }

            replMap.put(parts[0], parts[1]);
        }

        for (String alias : replMap.keySet()) {
            s = s.replaceAll(alias, replMap.get(alias));
        }

        return s;
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
                String output = ProcessUtils.runTerminatingProcess(
                        this.properties.getProperty(SWIPL_BIN) + " --dump-runtime-variables")
                        .getFirstValue();
                String[] lines = output.split("\n");
                String value = "";
                for (String line : lines) {
                    if (line.startsWith("PLBASE")) {
                        value = line;
                    }
                }

                String path = value.split("=")[1];

                this.swiplHome = path.substring(1, path.length() - 2);

                if (!this.swiplHome.endsWith(File.separator)) {
                    this.swiplHome = this.swiplHome + File.separator;
                }
            } catch (IOException e) {
                // TODO Auto-generated catch block
                e.printStackTrace();
            } catch (InterruptedException e) {
                // TODO Auto-generated catch block
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
                String output = ProcessUtils.runTerminatingProcess(
                        this.properties.getProperty(SWIPL_BIN) + " --dump-runtime-variables")
                        .getFirstValue();
                String[] lines = output.split("\n");
                String value = "";
                String path = "";
                for (String line : lines) {
                    if (line.startsWith("PLLIBDIR")) {
                        value = line;
                        path = value.split("=")[1];
                    }
                }

                if (value.equals("")) {

                    for (String line : lines) {
                        if (line.startsWith("PLARCH")) {
                            value = line;
                        }
                    }

                    if (value.equals("")) {
                        logger.error("$PLARCH is undefined as well.");
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
            } catch (IOException e) {
                // TODO Auto-generated catch block
                e.printStackTrace();
            } catch (InterruptedException e) {
                // TODO Auto-generated catch block
                e.printStackTrace();
            }
        }

        return this.swiplLib;
    }

    public void updateValueForLdPreload(String newValue) {
        this.updateValue("SWI_PROLOG_LIBSWIPL_PATH", newValue);
    }

    public void updateValueForLdLibraryPath(String newValue) {
        this.updateValue("SWI_PROLOG_LIBRARIES_PATH", newValue);
    }

    public String getDefaultOutputPath() {
        String defaultPath = "./target/generated-sources/";

        String configValue = (String) this.properties.getOrDefault("SYSTEM_DEFAULT_OUTPUT_PATH",
                "./target/generated-sources/");

        if (configValue.isEmpty()) {
            return defaultPath;
        } else {
            return configValue;
        }
    }

    private void updateValue(String name, String newValue) {
        Parameters params = new Parameters();
        FileBasedConfigurationBuilder<FileBasedConfiguration> builder = new FileBasedConfigurationBuilder<FileBasedConfiguration>(
                PropertiesConfiguration.class)
                        .configure(params.properties().setFileName(CONFIG_PATH));
        Configuration config;
        try {
            config = builder.getConfiguration();
            config.setProperty(name, newValue);
            builder.save();
        } catch (ConfigurationException e) {
            logger.error("Updating \"" + name + "\" failed.");
        }
    }

    public void openConfigFileForEditing() throws ExternalSoftwareUnavailableException {
        String editorExecutable = "";

        try {
            Process process = new ProcessBuilder("xdg-open", this.configFile.getAbsolutePath())
                    .directory(null).start();
            process.waitFor();
            return;
        } catch (IOException e) {
            // TODO
        } catch (InterruptedException e) {
            // TODO
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
            Process process = new ProcessBuilder(editorExecutable,
                    this.configFile.getAbsolutePath()).directory(null).start();
            process.waitFor();
        } catch (InterruptedException e) {
            // TODO
        } catch (IOException e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
        }
    }
}
