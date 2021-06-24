package com.fr2501.util;

import java.io.File;
import java.io.IOException;
import java.lang.reflect.Field;
import java.time.LocalDateTime;
import java.time.format.DateTimeFormatter;
import java.util.Map;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import com.fr2501.virage.core.VirageCore;

/**
 * A set of system utility functions.
 *
 */
public class SystemUtils {
  private static Logger logger = LogManager.getRootLogger();

  // TODO This is terrible and I know it. "export" is not possible from Java?
  /**
   * A method to set environment variables on Unix systems.

   * @param name the environment variable to be changed
   * @param value the new value of said variable
   */
  @SuppressWarnings("unchecked")
  public static void setUnixEnvironmentVariable(String name, String value) {
    logger.info("Attempting to change environment variable " + name + " to " + value);
    logger.info("Old value: " + System.getenv(name));

    Map<String, String> env = System.getenv();

    Field field;
    try {
      field = env.getClass().getDeclaredField("m");

      field.setAccessible(true);
      ((Map<String, String>) field.get(env)).put(name, value);
    } catch (NoSuchFieldException e) {
      // TODO Auto-generated catch block
      e.printStackTrace();
    } catch (SecurityException e) {
      // TODO Auto-generated catch block
      e.printStackTrace();
    } catch (IllegalArgumentException e) {
      // TODO Auto-generated catch block
      e.printStackTrace();
    } catch (IllegalAccessException e) {
      // TODO Auto-generated catch block
      e.printStackTrace();
    }

    logger.info("New value: " + System.getenv(name));
    if (!System.getenv(name).equals(value)) {
      logger.error("Setting environment variable " + name + " to " + value + " failed.");
    }
  }

  // See
  // https://stackoverflow.com/questions/5419039/is-djava-library-path-equivalent-to-system-setpropertyjava-library-path
  /**
   * A method to add paths to LD_LIBRARY_PATH. If possible, do not use this.

   * @param s the path to be added
   * @throws IOException if adding s to LD_LIBRARY_PATH is not possible
   */
  public static void addDirToLibraryPath(String s) throws IOException {
    try {
      // This enables the java.library.path to be modified at runtime
      // From a Sun engineer at http://forums.sun.com/thread.jspa?threadID=707176
      //
      Field field = ClassLoader.class.getDeclaredField("usr_paths");
      field.setAccessible(true);
      String[] paths = (String[]) field.get(null);
      for (int i = 0; i < paths.length; i++) {
        if (s.equals(paths[i])) {
          return;
        }
      }
      String[] tmp = new String[paths.length + 1];
      System.arraycopy(paths, 0, tmp, 0, paths.length);
      tmp[paths.length] = s;
      field.set(null, tmp);
      System.setProperty("java.library.path", 
          System.getProperty("java.library.path") + File.pathSeparator + s);
    } catch (IllegalAccessException e) {
      throw new IOException("Failed to get permissions to set library path");
    } catch (NoSuchFieldException e) {
      throw new IOException("Failed to get field handle to set library path");
    }
  }
  
  public static String getTime() {
    DateTimeFormatter dtf = DateTimeFormatter.ofPattern("yyyy-MM-dd HH:mm:ss");
    LocalDateTime now = LocalDateTime.now();
    
    return dtf.format(now);
  }
}
