package com.fr2501.virage.jobs;

import com.fr2501.virage.core.ConfigReader;
import com.fr2501.virage.core.VirageUserInterface;
import com.fr2501.virage.isabelle.IsabelleFrameworkExtractor;
import com.fr2501.virage.types.ExternalSoftwareUnavailableException;
import com.fr2501.virage.types.FrameworkRepresentation;
import com.fr2501.virage.types.IsabelleBuildFailedException;
import com.fr2501.virage.types.MalformedSettingsValueException;

/**
 * A {@link VirageJob} to extract a {@link FrameworkRepresentation} from an Isabelle session.
 *
 * @author VeriVote
 */
public final class VirageExtractJob extends VirageJobWithExplicitResult<FrameworkRepresentation> {
    /**
     * The Isabelle session name.
     */
    private final String sessionName;
    /**
     * The path to a ROOT file.
     */
    private final String path;
    /**
     * The name of the (E)PL file to be generated.
     */
    private final String fileName;

    /**
     * Simple constructor to be used when an arbitrary new (E)PL file
     * shall be created.
     *
     * @param issuer the issuer
     * @param pathValue the path to the session
     * @param sessionNameValue the name of the session
     */
    public VirageExtractJob(final VirageUserInterface issuer, final String pathValue,
            final String sessionNameValue) {
        this(issuer, pathValue, sessionNameValue, null);
    }

    /**
     * Simple constructor.
     *
     * @param issuer the issuer
     * @param pathValue the path to the session
     * @param sessionNameValue the name of the session
     * @param fileNameValue the name of the (E)PL file to be generated.
     */
    public VirageExtractJob(final VirageUserInterface issuer, final String pathValue,
            final String sessionNameValue, final String fileNameValue) {
        super(issuer);

        this.sessionName = sessionNameValue;
        this.path = pathValue;
        this.fileName = fileNameValue;
    }

    @Override
    protected void concreteExecute()
            throws ExternalSoftwareUnavailableException, IsabelleBuildFailedException,
            MalformedSettingsValueException {
        final IsabelleFrameworkExtractor extractor = new IsabelleFrameworkExtractor();
        final FrameworkRepresentation framework = extractor.extract(this.path, this.sessionName,
                this.fileName);
        framework.setTheoryPath(this.path);
        framework.setSessionName(this.sessionName);

        this.result = framework;
    }

    @Override
    public boolean externalSoftwareAvailable() {
        return ConfigReader.getInstance().hasIsabelle();
    }

    @Override
    public String getDescription() {
        return "Extracting (E)PL file ...";
    }

    @Override
    public String presentConcreteResult() {
        return "Extracted (E)PL file \'" + this.result.getAbsolutePath() + "\' from \'" + this.path
                + "\'.";
    }
}
