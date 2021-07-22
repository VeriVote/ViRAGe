package com.fr2501.virage.jobs;

import com.fr2501.virage.core.ConfigReader;
import com.fr2501.virage.core.VirageUserInterface;
import com.fr2501.virage.isabelle.IsabelleFrameworkExtractor;
import com.fr2501.virage.types.ExternalSoftwareUnavailableException;
import com.fr2501.virage.types.FrameworkRepresentation;
import com.fr2501.virage.types.IsabelleBuildFailedException;

/**
 * A {@link VirageJob} to extract a {@link FrameworkRepresentation} from an Isabelle session.
 *
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
     * @param path the path to the session
     * @param sessionName the name of the session
     */
    public VirageExtractJob(final VirageUserInterface issuer, final String path,
            final String sessionName) {
        this(issuer, path, sessionName, null);
    }

    /**
     * Simple constructor.
     *
     * @param issuer the issuer
     * @param path the path to the session
     * @param sessionName the name of the session
     * @param fileName the name of the (E)PL file to be generated.
     */
    public VirageExtractJob(final VirageUserInterface issuer, final String path,
            final String sessionName, final String fileName) {
        super(issuer);

        this.sessionName = sessionName;
        this.path = path;
        this.fileName = fileName;
    }

    @Override
    protected void concreteExecute()
            throws ExternalSoftwareUnavailableException, IsabelleBuildFailedException {
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
