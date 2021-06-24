package com.fr2501.virage.jobs;

import com.fr2501.util.Pair;
import com.fr2501.virage.core.ConfigReader;
import com.fr2501.virage.core.VirageUserInterface;
import com.fr2501.virage.isabelle.IsabelleProofChecker;
import java.io.File;

/**
 * A {@link VirageJob} that invokes Isabelle to automatically attempt proof verification.
 *
 */
public class VirageIsabelleVerifyJob extends VirageJobWithExplicitResult<Pair<Boolean, File>> {
  private IsabelleProofChecker checker;

  private File file;

  /**
   * Simple constructor.

   * @param issuer the issuing ui
   * @param file the file
   */
  public VirageIsabelleVerifyJob(VirageUserInterface issuer, File file) {
    super(issuer);

    this.file = file;
  }

  @Override
  protected void concreteExecute() throws Exception {
    this.checker = this.executingCore.getIsabelleProofChecker();

    this.result = this.checker.verifyTheoryFile(this.file,
        this.executingCore.getFrameworkRepresentation());
  }

  @Override
  public boolean externalSoftwareAvailable() {
    return (ConfigReader.getInstance().hasIsabelle());
  }

  @Override
  public String presentConcreteResult() {
    return "Isabelle theory " + this.file.getAbsolutePath() + " was verified automatically.";
  }

  @Override
  public String getDescription() {
    return "Verifying Isabelle theory ...";
  }

}
