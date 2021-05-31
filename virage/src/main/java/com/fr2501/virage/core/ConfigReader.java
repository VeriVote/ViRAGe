package com.fr2501.virage.core;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStream;
import java.util.Collections;
import java.util.LinkedList;
import java.util.List;
import java.util.Properties;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import org.jpl7.JPL;

import com.fr2501.util.Pair;
import com.fr2501.util.ProcessUtils;
import com.fr2501.virage.types.ExternalSoftwareUnavailableException;

public class ConfigReader {
  Logger logger = LogManager.getRootLogger();
  
  private static final String LIST_SEPARATOR = ";";
  
  private static final String SCALA_COMPILER = "scala_compiler";
  private static final String ISABELLE_HOME = "isabelle_home";
  private static final String SWIPL_HOME = "swipl_home";
  private static final String SWIPL_LIB = "swipl_lib";
  
  private static final String ISA_EXE = "/bin/isabelle";
  
  private static final String INSTALL_PLEASE = "Please install if necessary and check config.properties!";
  private static final String SEPARATOR = "----------";
  
  private boolean isabelleAvailable = true;
  private boolean scalacAvailable = true;
  private boolean swiplAvailable = true;
  private boolean jplAvailable = true;

  private Properties properties;

  private static ConfigReader instance;

  private ConfigReader() {
    try {
      this.readConfigFile();
    } catch (IOException e) {
      // TODO Auto-generated catch block
      e.printStackTrace();
    }
  }

  public static ConfigReader getInstance() {
    if (instance == null) {
      instance = new ConfigReader();
    }

    return instance;
  }

  public void readConfigFile() throws IOException {
    this.properties = new Properties();

    InputStream input = this.getClass().getClassLoader().getResourceAsStream("config.properties");

    this.properties.load(input);

    /*System.out.println("Properties: ");
    for(Object prop: this.properties.keySet()) {
      System.out.println("\t" + prop.toString() + ": " + this.properties.get(prop));
    }*/
  }
  
  public void checkAvailabilityAndPrintVersions() {
    // SCALA
    try {
      ProcessUtils.runTerminatingProcessAndPrintOutput(this.properties.get(SCALA_COMPILER) + " -version");
    } catch (IOException e) {
      logger.warn("No Scala compiler found! " + INSTALL_PLEASE);
      this.scalacAvailable = false;
    } catch (InterruptedException e) {
      // TODO Auto-generated catch block
      e.printStackTrace();
    }
    
    // ISABELLE
    try {
      ProcessUtils.runTerminatingProcessAndPrintOutput(this.getIsabelleExecutable() + " version");
    } catch (IOException e) {
      logger.warn("Isabelle not found! " + INSTALL_PLEASE);
      this.isabelleAvailable = false;
    } catch (InterruptedException e) {
      // TODO Auto-generated catch block
      e.printStackTrace();
    } catch (ExternalSoftwareUnavailableException e) {
      // TODO Auto-generated catch block
      e.printStackTrace();
    }
    
//    // SWIPL
//    try {
//      ProcessUtils.runTerminatingProcessAndPrintOutput(this.properties.get(SWIPL_LIB) + "swipl --version");
//    } catch (IOException e) {
//      logger.warn("SWI-Prolog not found! " + INSTALL_PLEASE);
//      this.isabelleAvailable = false;
//    } catch (InterruptedException e) {
//      // TODO Auto-generated catch block
//      e.printStackTrace();
//    }
    
    File file = new File(this.properties.get(SWIPL_HOME) + "lib/jpl.jar");
    if(!file.exists()) {
      this.logger.error("No jpl.jar found! " + INSTALL_PLEASE);
    } else {
      System.out.println("JPL version " + JPL.version_string());
    }
  }
  
  public String getIsabelleExecutable() throws ExternalSoftwareUnavailableException {
    if(!this.isabelleAvailable) {
      throw new ExternalSoftwareUnavailableException();
    }
    
    return this.properties.get(ISABELLE_HOME) + ISA_EXE;
  }
  
  public boolean hasIsabelle() {
    return this.isabelleAvailable;
  }

  public List<String> getIsabelleTactics() {
    return this.readAndSplitList("isabelle_tactics");
  }

  public List<Pair<String, String>> getTypeSynonyms() {
    List<Pair<String, String>> res = new LinkedList<Pair<String, String>>();
    List<String> typeSynonyms = this.readAndSplitList("type_synonyms");

    for (String synonym : typeSynonyms) {
      String[] splits = synonym.split("->");

      if (splits.length != 2)
        throw new IllegalArgumentException();

      res.add(new Pair<String, String>(splits[0], splits[1]));
    }

    return res;
  }

  public List<String> getAtomicTypes() {
    return this.readAndSplitList("atomic_types");
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
    return this.readAndSplitList("additional_properties");
  }

  public boolean hasScalaCompiler() {
    return this.scalacAvailable;
  }

  public String getScalaCompiler() throws ExternalSoftwareUnavailableException {
    if(!this.hasScalaCompiler()) {
      throw new ExternalSoftwareUnavailableException();
    }
    
    return this.properties.getProperty("scala_compiler");
  }

  public String getIsabelleHome() throws ExternalSoftwareUnavailableException {
    if(!this.isabelleAvailable) {
      throw new ExternalSoftwareUnavailableException();
    }
    
    return this.properties.getProperty("isabelle_home");
  }

  public String getIsabelleSessionDir() throws ExternalSoftwareUnavailableException {
    if(!this.isabelleAvailable) {
      throw new ExternalSoftwareUnavailableException();
    }
    
    String s = this.properties.getProperty("isabelle_session_dir");
    
    s = s.replace("~", System.getProperty("user.home"));
    
    return s;
  }

  public boolean hasPathToRootFile() {
    return this.properties.containsKey("path_to_root_file");
  }

  public String getPathToRootFile() {
    return this.properties.getProperty("path_to_root_file");
  }

  public boolean hasSessionName() {
    return this.properties.containsKey("session_name");
  }

  public String getSessionName() {
    return this.properties.getProperty("session_name");
  }

  public boolean hasJPL() {
    return this.jplAvailable;
  }
  
  public String getSwiplHome() {
    return this.properties.getProperty("swipl_home");
  }
  
  public String getSwiplLib() {
    return this.properties.getProperty(SWIPL_LIB);
  }
}
