package com.fr2501.virage.jobs;

import java.io.File;
import java.util.List;

import com.fr2501.virage.core.VirageUserInterface;
import com.fr2501.virage.isabelle.IsabelleTheoryGenerator;
import com.fr2501.virage.types.CompositionProof;

/**
 * A {@link VirageJob} used to generate Isabelle code.
 *
 * @author VeriVote
 */
public final class VirageIsabelleGenerateJob extends VirageJobWithExplicitResult<File> {
    /**
     * The composition.
     */
    private final String composition;
    /**
     * The proofs to be contained within the theory.
     */
    private final List<CompositionProof> proofs;
    /**
     * Path where the .thy-file will be saved.
     */
    private final String outputPath;

    /**
     * The Isabelle theory generator to be used.
     */
    private IsabelleTheoryGenerator generator;

    /**
     * Simple constructor.
     *
     * @param issuer the issuing ui
     * @param compositionValue the composition
     * @param proofsValue the proofs
     * @param outputPathValue the path for the generated theories
     */
    public VirageIsabelleGenerateJob(final VirageUserInterface issuer,
            final String compositionValue, final List<CompositionProof> proofsValue,
            final String outputPathValue) {
        super(issuer);

        this.composition = compositionValue;
        this.proofs = proofsValue;
        this.outputPath = outputPathValue;
    }

    @Override
    public boolean externalSoftwareAvailable() {
        return true;
    }

    @Override
    public String getDescription() {
        return "Generating Isabelle theory ...";
    }

    @Override
    public String presentConcreteResult() {
        return "Generated theory file at \'" + this.outputPath + "\'.";
    }

    @Override
    protected void concreteExecute() throws Exception {
        this.generator = this.executingCore.getIsabelleTheoryGenerator();

        this.result = this.generator.generateTheoryFile(this.composition, this.proofs,
                this.outputPath);
    }
}
