package edu.kit.kastel.formal.virage.jobs;

import edu.kit.kastel.formal.util.StringUtils;
import edu.kit.kastel.formal.virage.core.ConfigReader;
import edu.kit.kastel.formal.virage.core.VirageUserInterface;
import edu.kit.kastel.formal.virage.isabelle.IsabelleFrameworkExtractor;
import edu.kit.kastel.formal.virage.prolog.PrologParser;
import edu.kit.kastel.formal.virage.types.FrameworkExtractionFailedException;
import edu.kit.kastel.formal.virage.types.FrameworkRepresentation;

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
    protected void concreteExecute() throws FrameworkExtractionFailedException {
        final IsabelleFrameworkExtractor extractor = new IsabelleFrameworkExtractor();
        final FrameworkRepresentation framework =
                extractor.extract(this.path, this.sessionName, this.fileName);
        framework.setTheoryPath(this.path);
        framework.setSessionName(this.sessionName);
        this.setResult(framework);
    }

    @Override
    public boolean externalSoftwareAvailable() {
        return ConfigReader.getInstance().hasIsabelle();
    }

    @Override
    public String getDescription() {
        return StringUtils.printCollection2(
                "Extracting", PrologParser.EPL_FILE,
                StringUtils.parenthesize(PrologParser.DOT_PL), "...");
    }

    @Override
    public String presentConcreteResult() {
        return StringUtils.appendPeriod(
                StringUtils.printCollection2(
                        "Extracted", PrologParser.EPL_FILE,
                        StringUtils.parenthesize(PrologParser.DOT_PL),
                        StringUtils.addQuotations(this.getResult().getAbsolutePath()), "from",
                        StringUtils.addQuotations(this.path)));
    }
}
