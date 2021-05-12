package com.fr2501.util;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.util.LinkedList;
import java.util.List;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

/**
 * 
 * Utility class to read files line by line.
 *
 */
public class SimpleFileReader {
  private BufferedReader reader;
  private final static Logger logger = LogManager.getLogger(SimpleFileReader.class.getName());

  /**
   * Reads the specified file line by line.
   * 
   * @param file the file to be read.
   * @return a list containing the lines of that file.
   * @throws IOException if reading the file is not possible.
   */
  public List<String> readFileByLine(File file) throws IOException {
    logger.info("Trying to read from file \"" + file + "\"");

    List<String> res = new LinkedList<String>();

    try {
      this.reader = new BufferedReader(new FileReader(file));

      String line = reader.readLine();
      while (line != null) {
        res.add(line);
        line = reader.readLine();
      }
    } catch (FileNotFoundException e) {
      logger.error("Invalid file.");
      throw e;
    } catch (IOException e) {
      logger.error("Something went wrong while reading the file.");
      throw e;
    } finally {
      try {
        if (this.reader != null) {
          this.reader.close();
        }
      } catch (IOException e) {
        logger.warn("Closing the FileWriter was impossible.");
      }
    }

    return res;
  }

  /**
   * Reads the specified file.
   * 
   * @param file the file to be read.
   * @return a String representing the contents of that file.
   * @throws IOException if reading the file is not possible.
   */
  public String readFile(File file) throws IOException {
    List<String> list = this.readFileByLine(file);

    String res = "";
    for (String s : list) {
      res += s + "\n";
    }

    return res;
  }
}
