package com.fr2501.virage.jobs;

import java.io.File;

import com.fr2501.virage.beast.CCodeGenerator;
import com.fr2501.virage.core.ConfigReader;
import com.fr2501.virage.core.VirageUserInterface;

/**
 * A {@link VirageJob} used to invoke Isabelle code generation.
 *
 * @author VeriVote
 */
public final class VirageGenerateCCodeJob extends VirageJobWithExplicitResult<File> {
    /**
     * The C code generator.
     */
    private CCodeGenerator generator;

    /**
     * The generation from which code shall be generated.
     */
    private final String composition;

    /**
     * Simple constructor.
     *
     * @param issuer the issuing ui
     * @param composition the composition
     */
    public VirageGenerateCCodeJob(final VirageUserInterface issuer, final String composition) {
        super(issuer);

        this.composition = composition;
    }

    @Override
    protected void concreteExecute() throws Exception {
        this.generator = this.executingCore.getCCodeGenerator();

        this.result = this.generator.getCCodeFromComposition(this.composition);
    }

    @Override
    public boolean externalSoftwareAvailable() {
        return ConfigReader.getInstance().hasIsabelle();
    }

    @Override
    public String getDescription() {
        return "Generating C code ...";
    }

    @Override
    public String presentConcreteResult() {
        return "Created C source file at \'" + this.result + "\'.";
    }
}
