package edu.kit.kastel.formal.virage.jobs;

import java.io.File;

import edu.kit.kastel.formal.virage.core.ConfigReader;
import edu.kit.kastel.formal.virage.core.VirageUserInterface;
import edu.kit.kastel.formal.virage.isabelle.IsabelleCodeGenerator;
import edu.kit.kastel.formal.virage.types.CodeGenerationFailedException;

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
     * @param issuer the issuing user interface
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
        return "Created executable JAR file at \'" + this.getResult() + "\'.";
    }

    @Override
    protected void concreteExecute() throws CodeGenerationFailedException {
        this.generator = this.getExecutingCore().getIsabelleCodeGenerator();
        this.setResult(this.generator.generateScalaCodeAndCompile(this.composition));
    }
}
