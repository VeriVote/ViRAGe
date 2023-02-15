package com.fr2501.virage.isabelle;

import java.io.BufferedReader;
import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.OutputStream;
import java.io.StringWriter;
import java.nio.charset.StandardCharsets;
import java.text.SimpleDateFormat;
import java.util.Date;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.apache.commons.io.IOUtils;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import com.fr2501.util.Pair;
import com.fr2501.util.ProcessUtils;
import com.fr2501.util.SimpleFileReader;
import com.fr2501.util.SimpleFileWriter;
import com.fr2501.util.SystemUtils;
import com.fr2501.virage.core.ConfigReader;
import com.fr2501.virage.types.ExternalSoftwareUnavailableException;
import com.fr2501.virage.types.FrameworkRepresentation;
import com.fr2501.virage.types.IsabelleBuildFailedException;

/**
 * This class connects ViRAGe to Isabelle and automatically invokes the Isabelle processes required
 * to attempt automatic proof verification. It is meant to be a singleton, as every instance would
 * spawn new processes.
 *
 * @author VeriVote
 */
public final class IsabelleProofChecker {
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
     * The sesion name variable.
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
    private String rootTemplate = "";
    /**
     * The LaTeX template.
     */
    private String texTemplate = "";

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
        this.runtime = Runtime.getRuntime();

        this.solvers = ConfigReader.getInstance().getIsabelleTactics();

        // Use scala-isabelle to build the session, as my own solution
        // might not terminate when session build fails.
        ScalaIsabelleFacade.buildSession(theoryPathValue, sessionNameValue);

        try {
            final String clString =
                ConfigReader.getInstance().getIsabelleExecutable()
                + " build -o browser_info -b -D `pwd`";
            final Process process = Runtime.getRuntime().exec(String.format(clString));
            process.waitFor();

            this.initServer();
            this.initClient(sessionNameValue, theoryPathValue);

            if (this.rootTemplate.isEmpty()) {
                StringWriter writer = new StringWriter();
                final InputStream rootTemplateStream = this.getClass().getClassLoader()
                        .getResourceAsStream("doc_root.template");
                try {
                    IOUtils.copy(rootTemplateStream, writer, StandardCharsets.UTF_8);
                } catch (final IOException e) {
                    LOGGER.error(e);
                }
                this.rootTemplate = writer.toString();

                writer = new StringWriter();
                final InputStream texTemplateStream = this.getClass().getClassLoader()
                        .getResourceAsStream("tex_root.template");
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

    /**
     * Creates singleton instance, if necessary, and returns it.
     *
     * @param sessionName a name for the session to be created
     * @param theoryPath the path to the theory folder
     * @return the instance
     * @throws ExternalSoftwareUnavailableException if Isabelle is unavailable
     * @throws IsabelleBuildFailedException if the build process fails
     */
    public static IsabelleProofChecker getInstance(final String sessionName,
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
        final String localSessionName = "ad_hoc_session_"
                + new SimpleDateFormat("yyyyMMddHHmmss").format(new Date());

        String result = this.rootTemplate.replace(SESSION_NAME_VAR, localSessionName)
                .replace(THEORY_NAME_VAR, theoryName);
        result = result.replace(PARENT_NAME_VAR, this.parentName);
        final SimpleFileWriter writer = new SimpleFileWriter();
        writer.writeToFile(theory.getParent() + File.separator + "ROOT", result);

        return localSessionName;
    }

    /**
     * Destroys the current instance and its associated Isabelle processes.
     */
    public void destroy() {
        this.client.destroy();
        this.server.destroy();

        instance = null;
    }

    private void generateProofDocument(final File theory, final String adHocSessionName,
            final String localTheoryPath) throws IOException, InterruptedException,
            IsabelleBuildFailedException, ExternalSoftwareUnavailableException {
        final String generatedPath = theory.getParent();

        final String document = "document";
        final File docFolder = new File(
                generatedPath + File.separator + document + File.separator);
        docFolder.mkdir();
        final String texDoc = generatedPath + File.separator + document + File.separator
                + "root.tex";
        final SimpleFileWriter writer = new SimpleFileWriter();
        writer.writeToFile(texDoc, this.texTemplate);

        final String isabelleCommand = ConfigReader.getInstance().getIsabelleExecutable()
                + " build -e -D " + generatedPath + " -D " + localTheoryPath
                + " -o quick_and_dirty -o browser_info -b " + adHocSessionName;

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
            ConfigReader.getInstance().getIsabelleExecutable() + " client -n " + SERVER_NAME;
        this.client = this.runtime.exec(String.format(clString));
        this.clientInput = this.client.getOutputStream();

        IsabelleClientObserver.start(this, this.client);

        this.sendCommandAndWaitForTermination("session_start {\"session\":\"" + localSessionName
                + "\"," + "\"dirs\": [\"" + localTheoryPath + "\"]}");
        this.sessionId = this.lastEvent.getValue("session_id");
    }

    private void initServer() throws IOException, ExternalSoftwareUnavailableException {
        final String clString =
            ConfigReader.getInstance().getIsabelleExecutable() + " server -n " + SERVER_NAME;
        this.server = this.runtime.exec(String.format(clString));

        // The server will send a message when startup is finished.
        // Contents are irrelevant, just wait for it to appear.
        final BufferedReader reader = new BufferedReader(
                new InputStreamReader(this.server.getInputStream()));
        while (!reader.ready()) {
            SystemUtils.semiBusyWaitingHelper();
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

            final Pattern pattern = Pattern.compile("_v[0-9]+" + IsabelleUtils.FILE_EXTENSION);
            final Matcher matcher = pattern.matcher(localTheoryPath);

            int fileVersion = 1;
            String theoryPathWithoutSuffix = localTheoryPath.substring(0,
                    localTheoryPath.length() - ".thy".length());
            if (matcher.find()) {
                final String fileVersionString = localTheoryPath.substring(matcher.start() + 2,
                        matcher.end() - 4);
                fileVersion = Integer.parseInt(fileVersionString) + 1;

                theoryPathWithoutSuffix = theoryPathWithoutSuffix.substring(0, matcher.start());
            }

            final String theoryName = theory.getName().substring(0, theory.getName().length() - 4);
            final String newTheoryPath = theoryPathWithoutSuffix + "_v" + fileVersion
                    + IsabelleUtils.FILE_EXTENSION;

            final String[] splits = newTheoryPath.split(File.separator);
            final String newTheoryName = splits[splits.length - 1].substring(0,
                    splits[splits.length - 1].length() - 4);

            String line = lines.get(lineNum);

            for (int i = 0; i < this.solvers.size() - 1; i++) {
                if (line.contains(this.solvers.get(i))) {
                    line = line.replace(this.solvers.get(i), this.solvers.get(i + 1));

                    lines.set(lineNum, line);

                    String result = "";
                    for (final String s : lines) {
                        String actualS = s;
                        if (s.contains(theoryName)) {
                            actualS = s.replace(theoryName, newTheoryName);
                        }

                        result += actualS + System.lineSeparator();
                    }

                    theory.delete();
                    writer.writeToFile(newTheoryPath, result);

                    return new File(newTheoryPath);
                }
            }

            return null;
        } catch (final IOException e) {
            throw new IllegalArgumentException();
        }
    }

    private void sendCommandAndWaitForOk(final String command) throws IOException {
        this.clientInput.write((command + System.lineSeparator()).getBytes());
        this.clientInput.flush();

        // TODO: There is probably a better solution for this.
        while (!(this.getLastEvent() instanceof IsabelleOkEvent)) {
            SystemUtils.semiBusyWaitingHelper();
        }

        this.lastEvent = new IsabelleMiscEvent();
    }

    private void sendCommandAndWaitForTermination(final String command) throws IOException {
        this.clientInput.write((command + System.lineSeparator()).getBytes());
        this.clientInput.flush();

        this.waitForFinish();
    }

    public synchronized void setFinished(final boolean newFinished) {
        this.finished = newFinished;
    }

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
            final FrameworkRepresentation framework) throws IOException, InterruptedException {
        String theoryPathLocal = theory.getCanonicalPath();
        this.parentName = framework.getSessionName();

        if (theoryPathLocal.endsWith(IsabelleUtils.FILE_EXTENSION)) {
            theoryPathLocal = theoryPathLocal.substring(0,
                    theoryPathLocal.length() - IsabelleUtils.FILE_EXTENSION.length());
        }

        LOGGER.info("Starting to verify " + theory + ". This might take some time.");
        String command = "use_theories {\"session_id\": \"" + this.sessionId + "\", "
                + "\"theories\": [\"" + theoryPathLocal + "\"]}";
        this.sendCommandAndWaitForTermination(command);

        final String result = this.lastEvent.getValue("ok");
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

            command = "purge_theories {\"session_id\": \"" + this.sessionId + "\", "
                    + "\"theories\": [\"" + theoryPathLocal + "\"]}";
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
        this.finished = false;
    }
}
