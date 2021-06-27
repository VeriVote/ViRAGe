package com.fr2501.virage.core;

import com.fr2501.util.Pair;
import com.fr2501.util.ProcessUtils;
import com.fr2501.virage.types.ExternalSoftwareUnavailableException;
import java.io.File;
import java.io.IOException;
import java.io.InputStream;
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

  private static final String INSTALL_PLEASE = 
      "Please install if necessary and check config.properties!";

  private boolean isabelleAvailable = true;
  private boolean swiplAvailable = true;
  private boolean jplAvailable = true;

  private String isabelleHome;
  private String swiplHome;
  private String swiplLib;
  private String isabelleSessionDir;

  private String configPath;

  private Properties properties;

  private static ConfigReader instance;
  
  private File configFile;

  private ConfigReader() {
    try {
      this.readConfigFile();
    } catch (IOException e) {
      // TODO Auto-generated catch block
      e.printStackTrace();
    }
  }

  /**
   * Creates instance if necessary, otherwise just returns it.

   * @return the instance
   */
  public static ConfigReader getInstance() {
    if (instance == null) {
      instance = new ConfigReader();
    }

    return instance;
  }

  /**
   * Reads the config.properties-file supplied to ViRAGe.

   * @throws IOException if reading the file is impossible
   */
  public void readConfigFile() throws IOException {
    this.properties = new Properties();

    InputStream input = this.getClass().getClassLoader().getResourceAsStream("config.properties");
    this.configFile = new File(
        this.getClass().getClassLoader().getResource("config.properties").getFile());
    this.configPath = this.configFile.getAbsolutePath();

    this.properties.load(input);
  }
  
  public Map<String, String> getAllProperties() {
    Map<String, String> result = new HashMap<String, String>();
    
    for (Object prop : this.properties.keySet()) {
      result.put(prop.toString(), this.properties.getProperty(prop.toString()));
    }
    
    return result;
  }

  /**
   * Checks whether all external software is available and prints
   * the version numbers of said software.
   */
  public void checkAvailabilityAndPrintVersions() {
    // JAVA
    System.out.println("Java version " + System.getProperty("java.version"));
    
    // ISABELLE
    try {
      ProcessUtils.runTerminatingProcessAndPrintOutput(this.getIsabelleExecutable() + " version");
    } catch (IOException e) {
      logger.warn("Isabelle not found! " + INSTALL_PLEASE + " (relevant option: ISABELLE_EXECUTABLE)");
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
      ProcessUtils.runTerminatingProcessAndPrintOutput(
          this.properties.get(SWIPL_BIN) + " --version");
    } catch (IOException e) {
      logger.warn("SWI-Prolog not found! " + INSTALL_PLEASE + " (relevant options: SWI_PROLOG_EXECUTABLE)");
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

    System.out.println("JPL version " + JPL.version_string());  
  }

  /**
   * Simple getter.

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
    return this.readAndSplitList("ISABELLE_TACTICS");
  }

  /**
   * Returns the list of type synonyms defined in "SESSION_SPECIFIC_TYPE_SYNONYMS".

   * @return the list
   */
  public List<Pair<String, String>> getTypeSynonyms() {
    List<Pair<String, String>> res = new LinkedList<Pair<String, String>>();
    List<String> typeSynonyms = this.readAndSplitList("SESSION_SPECIFIC_TYPE_SYNONYMS");

    for (String synonym : typeSynonyms) {
      String[] splits = synonym.split("->");

      if (splits.length != 2) {
        throw new IllegalArgumentException();
      }

      res.add(new Pair<String, String>(splits[0], splits[1]));
    }

    return res;
  }

  public List<String> getAtomicTypes() {
    return this.readAndSplitList("SESSION_SPECIFIC_ATOMIC_TYPES");
  }

  private List<String> readAndSplitList(String key) {
    String list = (String) this.properties.get(key);
    String[] splits = list.split(LIST_SEPARATOR);

    List<String> result = new LinkedList<String>();
    for (int i = 0; i < splits.length; i++) {
      result.add(splits[i]);
    }

    return result;
  }

  public List<String> getAdditionalProperties() {
    return this.readAndSplitList("SESSION_SPECIFIC_ASSUMPTIONS");
  }

  /**
   * Retrieves the path to $ISABELLE_HOME.

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

  private String computeIsabelleHome() throws IOException, 
      InterruptedException, ExternalSoftwareUnavailableException {
    String output = ProcessUtils.runTerminatingProcess(
        this.getIsabelleExecutable() + " getenv ISABELLE_HOME").getFirstValue();

    return (output.split("=")[1].trim());
  }

  /**
   * Retrieves the Isabelle session directory.

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
    String output = ProcessUtils.runTerminatingProcess(
        this.getIsabelleExecutable() + " getenv ISABELLE_HOME_USER").getFirstValue();

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
  
  /**
   * Retrieves the SWI-Prolog home directory.

   * @return the directory
   * @throws ExternalSoftwareUnavailableException if swipl is unavailable
   */
  public String getSwiplHome() throws ExternalSoftwareUnavailableException {
    if (!this.swiplAvailable) {
      throw new ExternalSoftwareUnavailableException();
    }

    if (this.swiplHome == null) {
      try {
        String output = ProcessUtils
            .runTerminatingProcess(this.properties.getProperty(SWIPL_BIN) 
                + " --dump-runtime-variables").getFirstValue();
        String[] lines = output.split("\n");
        String value = "";
        for (String line : lines) {
          if (line.startsWith("PLBASE")) {
            value = line;
          }
        }

        String path = value.split("=")[1];
        this.swiplHome = path.substring(1, path.length() - 2);
      } catch (IOException e) {
        // TODO Auto-generated catch block
        e.printStackTrace();
      } catch (InterruptedException e) {
        // TODO Auto-generated catch block
        e.printStackTrace();
      }
    }

    return this.swiplHome + File.separator;
  }

  // TODO: De-spaghettize
  /**
   * Retrieves the SWI-Prolog library directory via "swipl --dump-runtime-variables".

   * @return the directory
   * @throws ExternalSoftwareUnavailableException if swipl is unavailable
   */
  public String getSwiplLib() throws ExternalSoftwareUnavailableException {
    if (!this.swiplAvailable) {
      throw new ExternalSoftwareUnavailableException();
    }

    if (this.swiplLib == null) {
      try {
        String output = ProcessUtils
            .runTerminatingProcess(this.properties.getProperty(SWIPL_BIN) 
                + " --dump-runtime-variables").getFirstValue();
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
            path = this.swiplHome + File.separator + "lib" + File.separator + tmp;
          }

        } else {
          path = path.substring(1, path.length() - 2);
        }

        this.swiplLib = path + File.separator;
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

  public String getConfigPath() {
    return this.configPath;
  }
  
  public void updateValueForLdPreload(String newValue) {
    this.updateValue("SWI_PROLOG_LIBSWIPL_PATH", newValue);
  }
  
  public void updateValueForLdLibraryPath(String newValue) {
    this.updateValue("SWI_PROLOG_LIBRARIES_PATH", newValue);
  }
  
  private void updateValue(String name, String newValue) {
    Parameters params = new Parameters();
    FileBasedConfigurationBuilder<FileBasedConfiguration> builder 
        = new FileBasedConfigurationBuilder<FileBasedConfiguration>(
        PropertiesConfiguration.class)
            .configure(params.properties().setFileName(this.configPath));
    Configuration config;
    try {
      config = builder.getConfiguration();
      config.setProperty(name, newValue);
      builder.save();
    } catch (ConfigurationException e) {
      logger.error("Updating \"" + name + "\" failed.");
    }
  }
}
