package com.fr2501.virage.jobs;

import com.fr2501.util.SimpleFileWriter;
import com.fr2501.virage.core.ConfigReader;
import com.fr2501.virage.core.VirageUserInterface;
import com.fr2501.virage.isabelle.IsabelleFrameworkExtractor;
import com.fr2501.virage.types.ExternalSoftwareUnavailableException;
import com.fr2501.virage.types.FrameworkRepresentation;
import com.fr2501.virage.types.IsabelleBuildFailedException;
import java.io.File;

/**
 * A {@link VirageJob} to extract a {@link FrameworkRepresentation} from an Isabelle session.
 *
 */
public class VirageExtractJob extends VirageJobWithExplicitResult<FrameworkRepresentation> {
  private String sessionName;
  private String path;

  /**
   * Simple constructor.

   * @param issuer the issuer
   * @param path the path to the session
   * @param sessionName the name of the session
   */
  public VirageExtractJob(VirageUserInterface issuer, String path, String sessionName) {
    super(issuer);

    this.sessionName = sessionName;
    this.path = path;
  }

  @Override
  protected void concreteExecute()
      throws ExternalSoftwareUnavailableException, IsabelleBuildFailedException {
    IsabelleFrameworkExtractor extractor = new IsabelleFrameworkExtractor();
    FrameworkRepresentation framework = extractor.extract(this.path, this.sessionName);
    framework.setTheoryPath(this.path);
    framework.setSessionName(this.sessionName);

    File frameworkFile = new File(this.path + File.separator + "framework.pl");
    SimpleFileWriter writer = new SimpleFileWriter();
    writer.writeToFile(frameworkFile.getAbsolutePath(), framework.toEplString());

    this.result = framework;
  }

  @Override
  public boolean externalSoftwareAvailable() {
    return (ConfigReader.getInstance().hasIsabelle());
  }
}
