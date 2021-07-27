package com.fr2501.virage.jobs;

import java.io.File;

import com.fr2501.util.Pair;
import com.fr2501.virage.core.ConfigReader;
import com.fr2501.virage.core.VirageUserInterface;
import com.fr2501.virage.isabelle.IsabelleProofChecker;

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
        if (this.result.getFirstValue()) {
            return "Isabelle theory \'" + this.result.getSecondValue().getAbsolutePath()
                    + "\' was verified successfully.";
        } else {
            return "Verification of Isabelle theory \'"
                    + this.result.getSecondValue().getAbsolutePath() + "\' failed.";
        }
    }

    @Override
    protected void concreteExecute() throws Exception {
        this.checker = this.executingCore.getIsabelleProofChecker();

        this.result = this.checker.verifyTheoryFile(this.file,
                this.executingCore.getFrameworkRepresentation());
    }

}
