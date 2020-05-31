package com.fr2501.virage.prolog;

import java.io.File;

import com.fr2501.virage.types.FrameworkRepresentation;

public interface ExtendedPrologParser {
	public FrameworkRepresentation parseFramework(File framework);
	public FrameworkRepresentation parseFramework(String framework);
}
