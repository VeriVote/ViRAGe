package com.fr2501.virage.prolog;

import java.io.File;
import java.io.IOException;

import com.fr2501.virage.types.FrameworkRepresentation;

public interface ExtendedPrologParser {
	public FrameworkRepresentation parseFramework(File file) throws IOException, MalformedEPLFileException;
}
