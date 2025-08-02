package edu.kit.kastel.formal.virage.jobs;

import java.io.File;
import java.util.List;

import edu.kit.kastel.formal.virage.core.VirageUserInterface;
import edu.kit.kastel.formal.virage.isabelle.IsabelleTheoryGenerator;
import edu.kit.kastel.formal.virage.types.CompositionProof;

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
     * Path where the <code>*.thy</code>-file will be saved.
     */
    private final String outputPath;

    /**
     * Simple constructor.
     *
     * @param issuer the issuing user interface
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
        return "Generated theory file at \'" + this.getResult().getAbsolutePath() + "\'.";
    }

    @Override
    protected void concreteExecute() {
        final IsabelleTheoryGenerator generator =
                this.getExecutingCore().getIsabelleTheoryGenerator();
        this.setResult(generator
                .generateTheoryFile(this.composition, this.proofs, this.outputPath));
    }
}
