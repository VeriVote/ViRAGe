package com.fr2501.virage.jobs;

import com.fr2501.virage.beast.CCodeGenerator;
import com.fr2501.virage.core.ConfigReader;
import com.fr2501.virage.core.VirageUserInterface;
import com.fr2501.virage.isabelle.IsabelleCodeGenerator;
import java.io.File;

/**
 * A {@link VirageJob} used to invoke Isabelle code generation.
 *
 */
public class VirageGenerateCCodeJob extends VirageJobWithExplicitResult<File> {
    private CCodeGenerator generator;

    private String composition;

    /**
     * Simple constructor.
     * 
     * @param issuer the issuing ui
     * @param composition the composition
     */
    public VirageGenerateCCodeJob(VirageUserInterface issuer, String composition) {
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
        return (ConfigReader.getInstance().hasIsabelle());
    }

    @Override
    public String presentConcreteResult() {
        return "Created C source file at \'" + this.result + "\'.";
    }

    @Override
    public String getDescription() {
        return "Generating C code ...";
    }
}
