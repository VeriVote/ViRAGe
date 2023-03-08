package edu.kit.kastel.formal.virage.jobs;

import java.io.File;

import edu.kit.kastel.formal.util.Pair;
import edu.kit.kastel.formal.virage.core.ConfigReader;
import edu.kit.kastel.formal.virage.core.VirageUserInterface;
import edu.kit.kastel.formal.virage.isabelle.IsabelleProofChecker;

/**
 * A {@link VirageJob} that invokes Isabelle to automatically attempt proof verification.
 *
 * @author VeriVote
 */
public final class VirageIsabelleVerifyJob
        extends VirageJobWithExplicitResult<Pair<Boolean, File>> {
    /**
     * The checker used to verify the proof.
     */
    private IsabelleProofChecker checker;

    /**
     * The theory file to be checked.
     */
    private final File file;

    /**
     * Simple constructor.
     *
     * @param issuer the issuing ui
     * @param fileValue the file
     */
    public VirageIsabelleVerifyJob(final VirageUserInterface issuer, final File fileValue) {
        super(issuer);

        this.file = fileValue;
    }

    @Override
    public boolean externalSoftwareAvailable() {
        return ConfigReader.getInstance().hasIsabelle();
    }

    @Override
    public String getDescription() {
        return "Verifying Isabelle theory ...";
    }

    @Override
    public String presentConcreteResult() {
        if (this.getResult().getFirstValue()) {
            return "Isabelle theory \'" + this.getResult().getSecondValue().getAbsolutePath()
                    + "\' was verified successfully.";
        } else {
            return "Verification of Isabelle theory failed.";
        }
    }

    @Override
    protected void concreteExecute() throws Exception {
        this.checker = this.getExecutingCore().getIsabelleProofChecker();

        this.setResult(this.checker.verifyTheoryFile(this.file,
                this.getExecutingCore().getFrameworkRepresentation()));
    }

}
