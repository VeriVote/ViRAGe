package edu.kit.kastel.formal.virage.jobs;

import java.io.File;

import edu.kit.kastel.formal.virage.beast.CCodeGenerator;
import edu.kit.kastel.formal.virage.core.VirageUserInterface;

/**
 * A {@link VirageJob} used to invoke Isabelle code generation.
 *
 * @author VeriVote
 */
public final class VirageGenerateCCodeJob extends VirageJobWithExplicitResult<File> {
    /**
     * The generation from which code shall be generated.
     */
    private final String composition;

    /**
     * Simple constructor.
     *
     * @param issuer the issuing user interface
     * @param compositionValue the composition
     */
    public VirageGenerateCCodeJob(final VirageUserInterface issuer, final String compositionValue) {
        super(issuer);
        this.composition = compositionValue;
    }

    @Override
    protected void concreteExecute() {
        final CCodeGenerator generator = this.getExecutingCore().getCCodeGenerator();
        this.setResult(generator.getCCodeFromComposition(this.composition));
    }

    @Override
    public boolean externalSoftwareAvailable() {
        return true;
    }

    @Override
    public String getDescription() {
        return "Generating C code ...";
    }

    @Override
    public String presentConcreteResult() {
        return "Created C source file at \'" + this.getResult() + "\'.";
    }
}
