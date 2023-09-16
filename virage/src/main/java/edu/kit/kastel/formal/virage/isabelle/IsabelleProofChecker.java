package edu.kit.kastel.formal.virage.isabelle;

import java.io.BufferedReader;
import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.OutputStream;
import java.io.StringWriter;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.text.SimpleDateFormat;
import java.util.Date;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.apache.commons.io.IOUtils;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import edu.kit.kastel.formal.util.Pair;
import edu.kit.kastel.formal.util.ProcessUtils;
import edu.kit.kastel.formal.util.SimpleFileReader;
import edu.kit.kastel.formal.util.SimpleFileWriter;
import edu.kit.kastel.formal.util.StringUtils;
import edu.kit.kastel.formal.util.SystemUtils;
import edu.kit.kastel.formal.virage.core.ConfigReader;
import edu.kit.kastel.formal.virage.types.ExternalSoftwareUnavailableException;
import edu.kit.kastel.formal.virage.types.FrameworkRepresentation;
import edu.kit.kastel.formal.virage.types.IsabelleBuildFailedException;

/**
 * This class connects ViRAGe to Isabelle and automatically invokes the Isabelle processes required
 * to attempt automatic proof verification. It is meant to be a singleton, as every instance would
 * spawn new processes.
 *
 * @author VeriVote
 */
public final class IsabelleProofChecker {
    /**
     * Parameter to override an Isabelle system option.
     */
    public static final String SYS_OPT = "-o";

    /**
     * Parameter to include an Isabelle build option.
     */
    public static final String BUILD_OPT = "-b";

    /**
     * Parameter to trigger Isabelle's quick and dirty option.
     */
    public static final String Q_AND_D_OPT = "quick_and_dirty";

    /**
     * Parameter to invoke the build process for Isabelle sessions.
     */
    public static final String BUILD_TOOL = "build";

    /**
     * Parameter to invoke Isabelle's scalac tool which wraps to the Scala compiler.
     */
    public static final String SCALAC_TOOL = "scalac";

    /**
     * Parameter to include Isabelle session directory.
     */
    public static final String INCL_SESS_DIR = "-d";

    /**
     * Parameter to include Isabelle session directory and select its sessions.
     */
    public static final String INCL_SEL_SESS_DIR = "-D";

    /**
     * Parameter to export files from session specification into file system.
     */
    public static final String EXPORT_FILES = "-e";

    /**
     * Parameter for Isabelle's document functionality.
     */
    private static final String DOC_OPTION = "doc";

    /**
     * Parameter for Isabelle's TeX functionality.
     */
    private static final String TEX_OPTION = "tex";

    /**
     * The singleton instance.
     */
    private static IsabelleProofChecker instance;

    /**
     * The server process name.
     */
    private static final String SERVER_NAME = "virage_isabelle_server";

    /**
     * The logger.
     */
    private static final Logger LOGGER = LogManager.getLogger(IsabelleProofChecker.class);

    /**
     * Parameter to set an explicit client/server name.
     */
    private static final String NAME_OPT = "-n";

    /**
     * String to refer to Isabelle logic session documents.
     */
    private static final String DOC_STRING = "document";

    /**
     * Parameter to manage resident Isabelle server processes.
     */
    private static final String SERVER_TOOL = "server";

    /**
     * Parameter to provide console interaction for Isabelle servers.
     */
    private static final String CLIENT_TOOL = "client";

    /**
     * String suffix for root options.
     */
    private static final String ROOT_SUFFIX = "_root";

    /**
     * Browser info option for command line call of Isabelle.
     */
    private static final String BROWSER_INFO = "browser_info";

    /**
     * Command to start a session.
     */
    private static final String SESSION_START_CMD = "session_start";

    /**
     * Event key for a session id.
     */
    private static final String SESSION_ID_EVENT_KEY = "session_id";

    /**
     * Parameter to pass the Unix PWD (print working directory) command.
     */
    private static final String PWD_CMD = "`pwd`";

    /**
     * The session name variable.
     */
    private static final String SESSION_NAME_VAR = "$SESSION_NAME";

    /**
     * The theory name variable.
     */
    private static final String THEORY_NAME_VAR = "$THEORY_NAME";

    /**
     * The parent name variable.
     */
    private static final String PARENT_NAME_VAR = "$PARENT_NAME";

    /**
     * The runtime.
     */
    private final Runtime runtime;

    /**
     * The server process.
     */
    private Process server;

    /**
     * The client process.
     */
    private Process client;

    /**
     * The client input stream.
     */
    private OutputStream clientInput;

    /**
     * The unique session ID.
     */
    private String sessionId;

    /**
     * The session name.
     */
    private String sessionName;

    /**
     * The theory path.
     */
    private String theoryPath;

    /**
     * The parent name. Defaults to "Pure" if nothing else is given.
     */
    private String parentName = "Pure";

    /**
     * The proof template.
     */
    private String rootTemplate = StringUtils.EMPTY;

    /**
     * The LaTeX template.
     */
    private String texTemplate = StringUtils.EMPTY;

    /**
     * The list of solvers to be used by Isabelle.
     */
    private List<String> solvers;

    /**
     * True iff verification is finished.
     */
    private boolean finished;

    /**
     * The last caught Isabelle event.
     */
    private IsabelleEvent lastEvent;

    private IsabelleProofChecker(final String sessionNameValue, final String theoryPathValue)
            throws ExternalSoftwareUnavailableException, IsabelleBuildFailedException {
        this.theoryPath = theoryPathValue;
        this.runtime = Runtime.getRuntime();
        this.solvers = ConfigReader.getInstance().getIsabelleTactics();

        // Use scala-isabelle to build the session, as my own solution
        // might not terminate when session build fails.
        ScalaIsabelleFacade.buildSession(theoryPathValue, sessionNameValue);

        try {
            final String clString =
                    StringUtils.printCollection2(
                            ConfigReader.getInstance().getIsabelleExecutable(),
                            BUILD_TOOL, SYS_OPT, BROWSER_INFO,
                            BUILD_OPT, INCL_SEL_SESS_DIR, PWD_CMD);
            final Process process = Runtime.getRuntime().exec(String.format(clString));
            process.waitFor();

            this.initServer();
            this.initClient(sessionNameValue, theoryPathValue);

            if (this.rootTemplate.isEmpty()) {
                StringWriter writer = new StringWriter();
                final InputStream rootTemplateStream = this.getClass().getClassLoader()
                        .getResourceAsStream(DOC_OPTION + ROOT_SUFFIX
                                                + IsabelleCodeGenerator.DOT_TMPL);
                try {
                    IOUtils.copy(rootTemplateStream, writer, StandardCharsets.UTF_8);
                } catch (final IOException e) {
                    LOGGER.error(e);
                }
                this.rootTemplate = writer.toString();

                writer = new StringWriter();
                final InputStream texTemplateStream = this.getClass().getClassLoader()
                        .getResourceAsStream(TEX_OPTION + ROOT_SUFFIX
                                                + IsabelleCodeGenerator.DOT_TMPL);
                try {
                    IOUtils.copy(texTemplateStream, writer, StandardCharsets.UTF_8);
                } catch (final IOException e) {
                    LOGGER.error(e);
                }
                this.texTemplate = writer.toString();
            }
        } catch (IOException | InterruptedException e) {
            LOGGER.error(e);
            e.printStackTrace();
        }
    }

    private static String sessionAndTheoriesCommand(final String session, final boolean hasId,
                                                    final String theoryDirectoriesOrNames,
                                                    final boolean isDirectory) {
        return "{\"session"
                + (hasId ? "_id" : StringUtils.EMPTY)
                + "\": \""
                + session + "\", "
                + "\""
                + (isDirectory ? "dirs" : "theories")
                + "\": [\"" + theoryDirectoriesOrNames + "\"]}";
    }

    private static synchronized void destroyInstance() {
        instance = null;
    }

    /**
     * Creates singleton instance, if necessary, and returns it.
     *
     * @param sessionName a name for the session to be created
     * @param theoryPath the path to the theory folder
     * @return the instance
     * @throws ExternalSoftwareUnavailableException if Isabelle is unavailable
     * @throws IsabelleBuildFailedException if the build process fails
     */
    public static synchronized IsabelleProofChecker getInstance(final String sessionName,
                                                                final String theoryPath)
            throws ExternalSoftwareUnavailableException, IsabelleBuildFailedException {
        if (instance == null || instance.sessionName == null
                || !instance.sessionName.equals(sessionName)
                || !instance.theoryPath.equals(theoryPath)) {
            instance = new IsabelleProofChecker(sessionName, theoryPath);
        }
        return instance;
    }

    private String buildSessionRoot(final String theoryName, final File theory) {
        // Session names MUST be universally unique, as Isabelle seems to be incapable
        // of
        // rebuilding single sessions without triggering full rebuilds.
        // TODO: Is there a way to do it?
        final String localSessionName =
                "ad_hoc_session_" + new SimpleDateFormat("yyyyMMddHHmmss").format(new Date());
        String result = this.rootTemplate
                .replace(SESSION_NAME_VAR, localSessionName).replace(THEORY_NAME_VAR, theoryName);
        result = result.replace(PARENT_NAME_VAR, this.parentName);
        final SimpleFileWriter writer = new SimpleFileWriter();
        writer.writeToFile(theory.getParent() + File.separator + IsabelleUtils.ROOT, result);
        return localSessionName;
    }

    /**
     * Destroys the current instance and its associated Isabelle processes.
     */
    public synchronized void destroy() {
        this.client.destroy();
        this.server.destroy();
        destroyInstance();
    }

    private void generateProofDocument(final File theory, final String adHocSessionName,
            final String localTheoryPath) throws IOException, InterruptedException,
            IsabelleBuildFailedException, ExternalSoftwareUnavailableException {
        final String generatedPath = theory.getParent();
        final File docFolder =
                SystemUtils.file(generatedPath + File.separator + DOC_STRING + File.separator);
        Files.createDirectory(docFolder.toPath());
        final String texDoc =
                generatedPath + File.separator + DOC_STRING + File.separator
                + IsabelleUtils.ROOT.toLowerCase() + IsabelleUtils.DOT_TEX;
        final SimpleFileWriter writer = new SimpleFileWriter();
        writer.writeToFile(texDoc, this.texTemplate);

        final String isabelleCommand =
                StringUtils.printCollection2(
                        ConfigReader.getInstance().getIsabelleExecutable(),
                        BUILD_TOOL, EXPORT_FILES, INCL_SEL_SESS_DIR, generatedPath,
                        INCL_SEL_SESS_DIR, localTheoryPath, SYS_OPT, Q_AND_D_OPT,
                        SYS_OPT, BROWSER_INFO, BUILD_OPT, adHocSessionName);
        final int status = ProcessUtils.runTerminatingProcessAndLogOutput(isabelleCommand);
        if (status != 0) {
            LOGGER.warn("Isabelle documentation generation failed.");
            throw new IsabelleBuildFailedException();
        }
    }

    private synchronized boolean getFinished() {
        return this.finished;
    }

    private synchronized IsabelleEvent getLastEvent() {
        return this.lastEvent;
    }

    private void initClient(final String localSessionName, final String localTheoryPath)
            throws IOException, ExternalSoftwareUnavailableException {
        final String clString =
                StringUtils.printCollection2(
                        ConfigReader.getInstance().getIsabelleExecutable(),
                        CLIENT_TOOL, NAME_OPT, SERVER_NAME);
        this.sessionName = localSessionName;
        this.client = this.runtime.exec(String.format(clString));
        this.clientInput = this.client.getOutputStream();

        IsabelleClientObserver.start(this, this.client);

        final String sessionAndTheoriesCommand =
                sessionAndTheoriesCommand(localSessionName, false, localTheoryPath, true);
        this.sendCommandAndWaitForTermination(
                StringUtils.printCollection2(SESSION_START_CMD, sessionAndTheoriesCommand));
        this.sessionId = this.lastEvent.getValue(SESSION_ID_EVENT_KEY);
    }

    private void initServer() throws IOException, ExternalSoftwareUnavailableException {
        final String clString =
                StringUtils.printCollection2(
                        ConfigReader.getInstance().getIsabelleExecutable(),
                        SERVER_TOOL, NAME_OPT, SERVER_NAME);
        this.server = this.runtime.exec(String.format(clString));
        // The server will send a message when startup is finished.
        // Contents are irrelevant, just wait for it to appear.
        try (BufferedReader br = new BufferedReader(new InputStreamReader(
                this.server.getInputStream(), StandardCharsets.UTF_8));) {
            while (!br.ready()) {
                SystemUtils.semiBusyWaitingHelper();
            }
        } catch (IOException e) {
            e.printStackTrace();
        }
    }

    /**
     * Applies the effects of a given event.
     *
     * @param evt the event
     */
    public synchronized void notify(final IsabelleEvent evt) {
        LOGGER.debug(evt.toString());
        this.lastEvent = evt;
        evt.applyEffects(this);
    }

    // This is the simplest, and probably slowest, solution to the problem that some
    // composition
    // rules can only be solved by certain solvers, essentially brute-forcing it.
    // Claim: If a proof method solves a step using a certain composition rule
    // *once*, it will
    // solve *all* steps that only use this rule. TODO: Investigate that.
    private File replaceSolver(final File theory, final int lineNum) {
        // return false;
        final SimpleFileReader reader = new SimpleFileReader();
        final SimpleFileWriter writer = new SimpleFileWriter();

        try {
            final List<String> lines = reader.readFileByLine(theory);
            final String localTheoryPath = theory.getCanonicalPath();
            final Pattern pattern = Pattern.compile("_v[0-9]+" + IsabelleUtils.DOT_THY);
            final Matcher matcher = pattern.matcher(localTheoryPath);

            int fileVersion = 1;
            String theoryPathWithoutSuffix =
                    localTheoryPath.substring(0,
                            localTheoryPath.length() - IsabelleUtils.DOT_THY.length());
            if (matcher.find()) {
                final String fileVersionString =
                        localTheoryPath.substring(matcher.start() + 2, matcher.end() - 4);
                fileVersion = Integer.parseInt(fileVersionString) + 1;
                theoryPathWithoutSuffix = theoryPathWithoutSuffix.substring(0, matcher.start());
            }

            final String theoryName = theory.getName().substring(0, theory.getName().length() - 4);
            final String newTheoryPath =
                    theoryPathWithoutSuffix + "_v" + fileVersion + IsabelleUtils.DOT_THY;

            final String[] splits =
                    newTheoryPath.split(File.separatorChar == '\\' ? "\\\\" : File.separator);
            final String newTheoryName =
                    splits[splits.length - 1].substring(0, splits[splits.length - 1].length() - 4);

            String line = lines.get(lineNum);
            for (int i = 0; i < this.solvers.size() - 1; i++) {
                if (line.contains(this.solvers.get(i))) {
                    line = line.replace(this.solvers.get(i), this.solvers.get(i + 1));
                    lines.set(lineNum, line);
                    String result = StringUtils.EMPTY;
                    for (final String s: lines) {
                        String actualS = s;
                        if (s.contains(theoryName)) {
                            actualS = s.replace(theoryName, newTheoryName);
                        }
                        result += actualS + System.lineSeparator();
                    }
                    Files.delete(theory.toPath());
                    writer.writeToFile(newTheoryPath, result);
                    return SystemUtils.file(newTheoryPath);
                }
            }
            return null;
        } catch (final IOException e) {
            throw new IllegalArgumentException();
        }
    }

    private void sendCommandAndWaitForOk(final String command) throws IOException {
        this.clientInput.write((command + System.lineSeparator()).getBytes(StandardCharsets.UTF_8));
        this.clientInput.flush();
        // TODO: There is probably a better solution for this.
        while (!(this.getLastEvent() instanceof IsabelleOkEvent)) {
            SystemUtils.semiBusyWaitingHelper();
        }
        this.lastEvent = new IsabelleMiscEvent();
    }

    private void sendCommandAndWaitForTermination(final String command) throws IOException {
        this.clientInput.write((command + System.lineSeparator()).getBytes(StandardCharsets.UTF_8));
        this.clientInput.flush();
        this.waitForFinish();
    }

    /**
     * Set the checker process finished value.
     *
     * @param newFinished the new finished value
     */
    private synchronized void setFinished(final boolean newFinished) {
        this.finished = newFinished;
    }

    /**
     * Set the checker process finished value to true.
     */
    public void finish() {
        this.setFinished(true);
    }

    /**
     * Set the checker process finished value to false.
     */
    public void resetFinished() {
        this.setFinished(false);
    }

    /**
     * Set new solvers.
     *
     * @param newSolvers the new solvers as a list
     */
    public void setSolvers(final List<String> newSolvers) {
        this.solvers = newSolvers;
    }

    /**
     * Attempts to automatically verify the given Isabelle theory. Might move the theory to a new
     * file in the process because Isabelle purge_theories does not actually lead to reloading if
     * the theory is used again and in the same file (might be a bug?).
     *
     * @param theory an Isabelle theory file
     * @param framework a framework representation
     * @return (true, newFile) if verification succeeds, (false, null) otherwise
     *
     * @throws IOException if file system interaction fails
     * @throws InterruptedException if execution is interrupted by the OS
     */
    public Pair<Boolean, File> verifyTheoryFile(final File theory,
                                                final FrameworkRepresentation framework)
                                                        throws IOException, InterruptedException {
        String theoryPathLocal = theory.getCanonicalPath();
        this.parentName = framework.getSessionName();
        if (theoryPathLocal.endsWith(IsabelleUtils.DOT_THY)) {
            theoryPathLocal =
                    theoryPathLocal.substring(0,
                            theoryPathLocal.length() - IsabelleUtils.DOT_THY.length());
        }
        LOGGER.info("Starting to verify " + theory + ". This might take some time.");
        final String sessionAndTheoriesCommand =
                sessionAndTheoriesCommand(this.sessionId, true, theoryPathLocal, false);
        String command = "use_theories " + sessionAndTheoriesCommand;
        this.sendCommandAndWaitForTermination(command);

        final String result = this.lastEvent.getValue(IsabelleUtils.SUCCESS_STRING.toLowerCase());
        if ("true".equals(result)) {
            LOGGER.info("Verification successful.");
            final String adHocSessionName = this.buildSessionRoot(
                    theory.getName().substring(0, theory.getName().length() - 4), theory);
            try {
                this.generateProofDocument(theory, adHocSessionName, framework.getTheoryPath());
            } catch (IOException | IsabelleBuildFailedException
                    | ExternalSoftwareUnavailableException e) {
                LOGGER.warn("No documentation could be generated.");
            }
            return new Pair<Boolean, File>(true, theory);
        } else {
            LOGGER.info("Verification failed. Attempting to solve automatically "
                    + "by employing different solvers.");
            final String errors = this.lastEvent.getValue("errors");

            command = "purge_theories "  + sessionAndTheoriesCommand;
            this.sendCommandAndWaitForOk(command);
            final Pattern pattern = Pattern.compile("line=[0-9]+");
            final Matcher matcher = pattern.matcher(errors);

            if (matcher.find()) {
                final String line = errors.substring(matcher.start(), matcher.end());
                // Isabelle starts counting at 1.
                final int lineNum = Integer.parseInt(line.split("=")[1]) - 1;
                final File newFile = this.replaceSolver(theory, lineNum);
                if (newFile != null) {
                    // The content of the file has changed, and this can
                    // only happen IsabelleUtils.SOLVERS.length times,
                    // so the recursive call is fine.
                    return this.verifyTheoryFile(newFile, framework);
                } else {
                    LOGGER.info("Automatic verification failed. "
                            + "You might be able to fix the errors manually within Isabelle.");
                }
            }
            return new Pair<Boolean, File>(false, null);
        }
    }

    private void waitForFinish() {
        while (!this.getFinished()) {
            SystemUtils.semiBusyWaitingHelper();
        }
        this.finish();
    }
}
