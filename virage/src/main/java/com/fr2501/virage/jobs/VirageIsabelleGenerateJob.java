package com.fr2501.virage.jobs;

import java.io.File;
import java.util.List;

import com.fr2501.virage.core.ConfigReader;
import com.fr2501.virage.core.VirageUserInterface;
import com.fr2501.virage.isabelle.IsabelleTheoryGenerator;
import com.fr2501.virage.types.CompositionProof;

/**
 * 
 * A {@link VirageJob} used to generate Isabelle code.
 *
 */
public class VirageIsabelleGenerateJob extends VirageJobWithExplicitResult<File> {
  private String composition;
  private List<CompositionProof> proofs;
  private String outputPath;

  private IsabelleTheoryGenerator generator;

  public VirageIsabelleGenerateJob(VirageUserInterface issuer, String composition, List<CompositionProof> proofs,
      String outputPath) {
    super(issuer);

    this.composition = composition;
    this.proofs = proofs;
    this.outputPath = outputPath;
  }

  @Override
  protected void concreteExecute() throws Exception {
    this.generator = this.executingCore.getIsabelleTheoryGenerator();

    this.result = this.generator.generateTheoryFile(this.composition, this.proofs, this.outputPath);
  }

  @Override
  public boolean externalSoftwareAvailable() {
    return true;
  }
}
