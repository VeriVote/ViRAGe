package com.fr2501.virage.jobs;

import com.fr2501.virage.core.ConfigReader;
import com.fr2501.virage.core.VirageUserInterface;
import com.fr2501.virage.isabelle.IsabelleCodeGenerator;
import java.io.File;

/**
 * A {@link VirageJob} used to invoke Isabelle code generation.
 *
 */
public class VirageIsabelleGenerateScalaJob extends VirageJobWithExplicitResult<File> {
  private IsabelleCodeGenerator generator;

  private String composition;

  public VirageIsabelleGenerateScalaJob(VirageUserInterface issuer, String composition) {
    super(issuer);

    this.composition = composition;
  }

  @Override
  protected void concreteExecute() throws Exception {
    this.generator = this.executingCore.getIsabelleCodeGenerator();

    this.result = this.generator.generateScalaCodeAndCompile(this.composition);
  }

  @Override
  public boolean externalSoftwareAvailable() {
    return (ConfigReader.getInstance().hasIsabelle()
        && ConfigReader.getInstance().hasScalaCompiler());
  }
}
