package com.fr2501.virage.prolog;

import java.io.File;
import java.util.List;

import com.fr2501.virage.types.FrameworkRepresentation;

public interface ExtendedPrologParser {
	public FrameworkRepresentation parseFramework(File file);
	FrameworkRepresentation parseFramework(List<String> representation);
}
