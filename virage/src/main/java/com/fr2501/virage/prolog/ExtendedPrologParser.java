package com.fr2501.virage.prolog;

import java.io.File;
import java.io.IOException;

import com.fr2501.virage.types.FrameworkRepresentation;

/**
 * 
 * A parser for the extended Prolog format developed for representation of the modular framework.
 *
 */
public interface ExtendedPrologParser {
	/**
	 * 
	 * @param file the file containing the framework representation in extended Prolog format.
	 * @return a {@link FrameworkRepresentation} containing the framework.
	 * @throws IOException if an error occurs while reading the file itself.
	 * @throws MalformedEPLFileException if the file can be read, but not parsed.
	 */
	public FrameworkRepresentation parseFramework(File file, boolean addDummies) throws IOException, MalformedEPLFileException;
}
