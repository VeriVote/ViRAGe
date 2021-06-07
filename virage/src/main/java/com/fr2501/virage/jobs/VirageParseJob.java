package com.fr2501.virage.jobs;

import com.fr2501.virage.core.VirageUserInterface;
import com.fr2501.virage.prolog.ExtendedPrologParser;
import com.fr2501.virage.prolog.MalformedEplFileException;
import com.fr2501.virage.types.FrameworkRepresentation;
import java.io.File;
import java.io.IOException;

/**
 * 
 * A {@link VirageJob} used to parse an (E)PL file and pass it to its executing core.
 *
 */
public class VirageParseJob extends VirageJobWithExplicitResult<FrameworkRepresentation> {
  private ExtendedPrologParser parser;

  private File file;

  public VirageParseJob(VirageUserInterface issuer, File file) {
    super(issuer);

    this.file = file;
  }

  @Override
  public void concreteExecute() throws IOException, MalformedEplFileException {
    this.parser = this.executingCore.getExtendedPrologParser();

    this.result = this.parser.parseFramework(this.file, true);
    this.executingCore.setFrameworkRepresentation(this.result);

  }

  @Override
  public FrameworkRepresentation getResult() {
    return this.result;
  }

  @Override
  public boolean externalSoftwareAvailable() {
    return true;
  }
}
