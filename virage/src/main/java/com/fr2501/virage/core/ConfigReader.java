package com.fr2501.virage.core;

import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStream;
import java.util.Collections;
import java.util.LinkedList;
import java.util.List;
import java.util.Properties;

import com.fr2501.util.Pair;

public class ConfigReader {
  private static final String LIST_SEPARATOR = ";";

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

    // TODO print properties + versions
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
    return this.properties.containsKey("scala_compiler");
  }

  public String getScalaCompiler() {
    return this.properties.getProperty("scala_compiler");
  }

  public String getIsabelleHome() {
    return this.properties.getProperty("isabelle_home");
  }

  public String getIsabelleSessionDir() {
    return this.properties.getProperty("isabelle_session_dir");
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

  public String getSWIPLHome() {
    return this.properties.getProperty("swipl_home");
  }

}
