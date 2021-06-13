package com.fr2501.util;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.Collection;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

/**
 * Utility class to write files line by line.
 *
 */
public class SimpleFileWriter {
  private FileWriter writer;
  private static final Logger logger = LogManager.getLogger(SimpleFileWriter.class.getName());

  /**
   * Writes Collection to file, with every item on its own line, creates file if
   * needed.

   * @param path       the file to be written to
   * @param collection the collection
   */
  public void writeToFile(String path, Collection<?> collection) {
    try {
      this.writer = new FileWriter(new File(path).getCanonicalFile());

      for (Object o : collection) {
        writer.write(o.toString() + "\n");
      }
    } catch (IOException e) {
      logger.error("Writing to " + path + " was impossible.");
    } finally {
      try {
        this.writer.close();
      } catch (IOException e) {
        logger.warn("Closing the FileWriter was impossible.");
      }
    }
  }

  /**
   * Writes String to file.

   * @param path     the file to be written to
   * @param contents the String to be written to the file
   */
  public void writeToFile(String path, String contents) {
    try {
      File file = new File(path).getCanonicalFile();

      this.writer = new FileWriter(file);
      this.writer.write(contents);
    } catch (IOException e) {
      logger.error("Writing to " + path + " was impossible.");
    } finally {
      try {
        this.writer.close();
      } catch (IOException e) {
        logger.warn("Closing the FileWriter was impossible.");
      }
    }
  }
}
