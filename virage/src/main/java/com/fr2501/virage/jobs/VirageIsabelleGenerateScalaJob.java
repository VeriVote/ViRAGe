package com.fr2501.virage.jobs;

import java.io.File;

import com.fr2501.virage.core.ConfigReader;
import com.fr2501.virage.core.VirageUserInterface;
import com.fr2501.virage.isabelle.IsabelleCodeGenerator;

/**
 * A {@link VirageJob} used to invoke Isabelle code generation.
 *
 * @author VeriVote
 */
public final class VirageIsabelleGenerateScalaJob extends VirageJobWithExplicitResult<File> {
    /**
     * The Isabelle Scala generator.
     */
    private IsabelleCodeGenerator generator;

    /**
     * The composition from which an implementation shall be generated.
     */
    private final String composition;

    /**
     * Simple constructor.
     *
     * @param issuer the issuing ui
     * @param compositionValue the composition
     */
    public VirageIsabelleGenerateScalaJob(final VirageUserInterface issuer,
            final String compositionValue) {
        super(issuer);

        this.composition = compositionValue;
    }

    @Override
    public boolean externalSoftwareAvailable() {
        return ConfigReader.getInstance().hasIsabelle();
    }

    @Override
    public String getDescription() {
        return "Generating and compiling Scala code ...";
    }

    @Override
    public String presentConcreteResult() {
        return "Created executable JAR file at \'" + this.result + "\'.";
    }

    @Override
    protected void concreteExecute() throws Exception {
        this.generator = this.getExecutingCore().getIsabelleCodeGenerator();

        this.result = this.generator.generateScalaCodeAndCompile(this.composition);
    }
}
