package com.fr2501.virage.prolog;

import com.fr2501.virage.types.FrameworkRepresentation;
import java.io.File;
import java.io.IOException;

/**
 * A parser for the extended Prolog format developed for representation of the modular framework.
 *
 */
public interface ExtendedPrologParser {
  /**
   * Parses a an EPL file.

   * @param file the file containing the framework representation in extended Prolog format.
   * @param addDummies true if dummy rules shall be added, false otherwise.
   * @return a {@link FrameworkRepresentation} containing the framework.
   * @throws IOException if an error occurs while reading the file itself.
   * @throws MalformedEplFileException if the file can be read, but not parsed.
   */
  public FrameworkRepresentation parseFramework(File file, boolean addDummies)
      throws IOException, MalformedEplFileException;
}
