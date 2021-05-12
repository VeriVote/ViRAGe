package com.fr2501.virage.jobs;

import java.io.File;
import java.io.IOException;

import com.fr2501.virage.core.VirageUserInterface;
import com.fr2501.virage.prolog.ExtendedPrologParser;
import com.fr2501.virage.prolog.MalformedEPLFileException;

/**
 * 
 * A {@link VirageJob} used to parse an (E)PL file and pass it to its executing
 * core.
 *
 */
public class VirageParseJob extends VirageJobWithoutExplicitResult {
  private ExtendedPrologParser parser;

  private File file;

  public VirageParseJob(VirageUserInterface issuer, File file) {
    super(issuer);

    this.file = file;
  }

  @Override
  public void concreteExecute() throws IOException, MalformedEPLFileException {
    this.parser = this.executingCore.getExtendedPrologParser();

    this.executingCore.setFrameworkRepresentation(this.parser.parseFramework(this.file, true));

  }

  @Override
  public Void getResult() {
    throw new UnsupportedOperationException();
  }
}
