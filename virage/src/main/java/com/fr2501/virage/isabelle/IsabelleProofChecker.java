package com.fr2501.virage.isabelle;

import com.fr2501.util.Pair;
import com.fr2501.util.ProcessUtils;
import com.fr2501.util.SimpleFileReader;
import com.fr2501.util.SimpleFileWriter;
import com.fr2501.virage.core.ConfigReader;
import com.fr2501.virage.types.ExternalSoftwareUnavailableException;
import com.fr2501.virage.types.FrameworkRepresentation;
import com.fr2501.virage.types.IsabelleBuildFailedException;
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

/**
 * This class connects ViRAGe to Isabelle and automatically invokes the Isabelle processes required
 * to attempt automatic proof verification. It is meant to be a singleton, as every instance would
 * spawn new processes.
 *
 */
public class IsabelleProofChecker {
    private static IsabelleProofChecker instance = null;
    private static final String SERVER_NAME = "virage_isabelle_server";

    private static final Logger logger = LogManager.getLogger(IsabelleProofChecker.class);

    private Runtime runtime;
    private Process server;
    private Process client;
    private OutputStream clientInput;

    private String sessionId;
    private String sessionName;
    private String theoryPath;
    // Default if nothing else is given.
    private String parentName = "Pure";

    private String rootTemplate = "";
    private static final String SESSION_NAME_VAR = "$SESSION_NAME";
    private static final String THEORY_NAME_VAR = "$THEORY_NAME";
    private static final String PARENT_NAME_VAR = "$PARENT_NAME";
    private String texTemplate = "";

    private List<String> solvers;

    boolean finished = false;
    IsabelleEvent lastEvent;

    private IsabelleProofChecker(String sessionName, String theoryPath)
            throws ExternalSoftwareUnavailableException, IsabelleBuildFailedException {
        this.runtime = Runtime.getRuntime();

        this.solvers = ConfigReader.getInstance().getIsabelleTactics();

        // Use scala-isabelle to build the session, as my own solution
        // might not terminate when session build fails.
        ScalaIsabelleFacade.buildSession(theoryPath, sessionName);

        try {
            // TODO: Remove quick_and_dirty as soon as possible (or make optional?)
            Process process = Runtime.getRuntime()
                    .exec(ConfigReader.getInstance().getIsabelleExecutable()
                            + " build -o browser_info -b -D `pwd`");
            process.waitFor();

            this.initServer();
            this.initClient(sessionName, theoryPath);

            if (this.rootTemplate.equals("")) {
                StringWriter writer = new StringWriter();
                InputStream rootTemplateStream = this.getClass().getClassLoader()
                        .getResourceAsStream("doc_root.template");
                try {
                    IOUtils.copy(rootTemplateStream, writer, StandardCharsets.UTF_8);
                } catch (IOException e) {
                    logger.error("Something went wrong.", e);
                }
                rootTemplate = writer.toString();

                writer = new StringWriter();
                InputStream texTemplateStream = this.getClass().getClassLoader()
                        .getResourceAsStream("tex_root.template");
                try {
                    IOUtils.copy(texTemplateStream, writer, StandardCharsets.UTF_8);
                } catch (IOException e) {
                    logger.error("Something went wrong.", e);
                }
                texTemplate = writer.toString();
            }
        } catch (Exception e) {
            logger.error("Something went wrong.", e);
            e.printStackTrace();
        }
    }

    private synchronized boolean getFinished() {
        return this.finished;
    }

    public synchronized void setFinished(boolean finished) {
        this.finished = finished;
    }

    public void setSolvers(List<String> solvers) {
        this.solvers = solvers;
    }

    /**
     * Creates singleton instance, if necessary, and returns it.
     * 
     * @param sessionName a name for the session to be created
     * @param theoryPath the path to the theory folder
     * @return the instance
     * @throws ExternalSoftwareUnavailableException
     * @throws IsabelleBuildFailedException
     */
    public static IsabelleProofChecker getInstance(String sessionName, String theoryPath)
            throws ExternalSoftwareUnavailableException, IsabelleBuildFailedException {
        if (instance == null || instance.sessionName == null
                || !instance.sessionName.equals(sessionName)
                || !instance.theoryPath.equals(theoryPath)) {
            instance = new IsabelleProofChecker(sessionName, theoryPath);
        }

        return instance;
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
    public Pair<Boolean, File> verifyTheoryFile(File theory, FrameworkRepresentation framework)
            throws IOException, InterruptedException {
        String theoryPath = theory.getCanonicalPath();
        this.parentName = framework.getSessionName();

        if (theoryPath.endsWith(IsabelleUtils.FILE_EXTENSION)) {
            theoryPath = theoryPath.substring(0,
                    theoryPath.length() - IsabelleUtils.FILE_EXTENSION.length());
        }

        logger.info("Starting to verify " + theory + ". This might take some time.");
        String command = "use_theories {\"session_id\": \"" + this.sessionId + "\", "
                + "\"theories\": [\"" + theoryPath + "\"]}";
        this.sendCommandAndWaitForTermination(command);

        String result = this.lastEvent.getValue("ok");
        if (result.equals("true")) {
            logger.info("Verification successful.");

            String adHocSessionName = this.buildSessionRoot(
                    theory.getName().substring(0, theory.getName().length() - 4), theory);
            try {
                this.generateProofDocument(theory, adHocSessionName, framework.getTheoryPath());
            } catch (Exception e) {
                logger.warn("No documentation could be generated.");
            }

            return new Pair<Boolean, File>(true, theory);
        } else {
            logger.info(
                    "Verification failed. Attempting to solve automatically by employing different solvers.");
            String errors = this.lastEvent.getValue("errors");

            command = "purge_theories {\"session_id\": \"" + this.sessionId + "\", "
                    + "\"theories\": [\"" + theoryPath + "\"]}";
            this.sendCommandAndWaitForOk(command);

            Pattern pattern = Pattern.compile("line=[0-9]+");
            Matcher matcher = pattern.matcher(errors);

            if (matcher.find()) {
                String line = errors.substring(matcher.start(), matcher.end());
                // Isabelle starts counting at 1.
                int lineNum = Integer.parseInt(line.split("=")[1]) - 1;

                File newFile = this.replaceSolver(theory, lineNum);
                if (newFile != null) {
                    // The content of the file has changed, and this can
                    // only happen IsabelleUtils.SOLVERS.length times,
                    // so the recursive call is fine.
                    return this.verifyTheoryFile(newFile, framework);
                } else {
                    logger.info("Automatic verification failed. "
                            + "You might be able to fix the errors manually within Isabelle.");
                }
            }

            return new Pair<Boolean, File>(false, null);
        }
    }

    private void generateProofDocument(File theory, String adHocSessionName, String theoryPath)
            throws IOException, InterruptedException, IsabelleBuildFailedException,
            ExternalSoftwareUnavailableException {
        String generatedPath = theory.getParent();

        File docFolder = new File(generatedPath + File.separator + "document" + File.separator);
        docFolder.mkdir();
        String texDoc = generatedPath + File.separator + "document" + File.separator + "root.tex";
        SimpleFileWriter writer = new SimpleFileWriter();
        writer.writeToFile(texDoc, this.texTemplate);

        String isabelleCommand = ConfigReader.getInstance().getIsabelleExecutable()
                + " build -e -D " + generatedPath + " -D " + theoryPath
                + " -o quick_and_dirty -o browser_info -b " + adHocSessionName;

        int status = ProcessUtils.runTerminatingProcessAndLogOutput(isabelleCommand);

        if (status != 0) {
            logger.warn("Isabelle documentation generation failed.");

            throw new IsabelleBuildFailedException();
        }
    }

    private String buildSessionRoot(String theoryName, File theory) {
        // Session names MUST be universally unique, as Isabelle seems to be incapable
        // of
        // rebuilding single sessions without triggering full rebuilds.
        // TODO: Is there a way to do it?
        String sessionName = "ad_hoc_session_"
                + new SimpleDateFormat("yyyyMMddHHmmss").format(new Date());

        String result = this.rootTemplate.replace(SESSION_NAME_VAR, sessionName)
                .replace(THEORY_NAME_VAR, theoryName);
        result = result.replace(PARENT_NAME_VAR, this.parentName);
        SimpleFileWriter writer = new SimpleFileWriter();
        writer.writeToFile(theory.getParent() + File.separator + "ROOT", result);

        return sessionName;
    }

    /**
     * Destroys the current instance and its associated Isabelle processes.
     */
    public void destroy() {
        this.client.destroy();
        this.server.destroy();

        instance = null;
    }

    /**
     * Applies the effects of a given event.
     * 
     * @param evt the event
     */
    public synchronized void notify(IsabelleEvent evt) {
        logger.debug(evt.toString());
        this.lastEvent = evt;
        evt.applyEffects(this);
    }

    private synchronized IsabelleEvent getLastEvent() {
        return this.lastEvent;
    }

    private void sendCommandAndWaitForTermination(String command) throws IOException {
        this.clientInput.write((command + "\n").getBytes());
        this.clientInput.flush();

        this.waitForFinish();
    }

    private void sendCommandAndWaitForOk(String command) throws IOException {
        this.clientInput.write((command + "\n").getBytes());
        this.clientInput.flush();

        // TODO: There is probably a better solution for this.
        while (!(this.getLastEvent() instanceof IsabelleOkEvent)) {

        }

        this.lastEvent = new IsabelleMiscEvent();
    }

    private void initServer() throws IOException, ExternalSoftwareUnavailableException {
        this.server = this.runtime.exec(
                ConfigReader.getInstance().getIsabelleExecutable() + " server -n " + SERVER_NAME);

        // The server will send a message when startup is finished.
        // Contents are irrelevant, just wait for it to appear.
        BufferedReader reader = new BufferedReader(
                new InputStreamReader(this.server.getInputStream()));
        while (!reader.ready()) {
        }
    }

    private void initClient(String sessionName, String theoryPath)
            throws IOException, ExternalSoftwareUnavailableException {
        this.client = this.runtime.exec(
                ConfigReader.getInstance().getIsabelleExecutable() + " client -n " + SERVER_NAME);
        this.clientInput = this.client.getOutputStream();

        IsabelleClientObserver.start(this, this.client);

        this.sendCommandAndWaitForTermination("session_start {\"session\":\"" + sessionName + "\","
                + "\"dirs\": [\"" + theoryPath + "\"]}");
        this.sessionId = this.lastEvent.getValue("session_id");
    }

    private void waitForFinish() {
        while (!this.getFinished()) {
        }
        this.finished = false;
    }

    // This is the simplest, and probably slowest, solution to the problem that some
    // composition
    // rules can only be solved by certain solvers, essentially brute-forcing it.
    // Claim: If a proof method solves a step using a certain composition rule
    // *once*, it will
    // solve *all* steps that only use this rule. TODO: Investigate that.
    private File replaceSolver(File theory, int lineNum) {
        // return false;

        SimpleFileReader reader = new SimpleFileReader();
        SimpleFileWriter writer = new SimpleFileWriter();

        try {
            List<String> lines = reader.readFileByLine(theory);
            String theoryPath = theory.getCanonicalPath();

            Pattern pattern = Pattern.compile("_v[0-9]+" + IsabelleUtils.FILE_EXTENSION);
            Matcher matcher = pattern.matcher(theoryPath);

            int fileVersion = 1;
            String theoryPathWithoutSuffix = theoryPath.substring(0, theoryPath.length() - 4);
            if (matcher.find()) {
                String fileVersionString = theoryPath.substring(matcher.start() + 2,
                        matcher.end() - 4);
                fileVersion = Integer.parseInt(fileVersionString) + 1;

                theoryPathWithoutSuffix = theoryPathWithoutSuffix.substring(0, matcher.start());
            }

            String theoryName = theory.getName().substring(0, theory.getName().length() - 4);
            String newTheoryPath = theoryPathWithoutSuffix + "_v" + fileVersion
                    + IsabelleUtils.FILE_EXTENSION;

            String[] splits = newTheoryPath.split(File.separator);
            String newTheoryName = splits[splits.length - 1].substring(0,
                    splits[splits.length - 1].length() - 4);

            String line = lines.get(lineNum);

            for (int i = 0; i < this.solvers.size() - 1; i++) {
                if (line.contains(this.solvers.get(i))) {
                    line = line.replace(this.solvers.get(i), this.solvers.get(i + 1));

                    lines.set(lineNum, line);

                    String result = "";
                    for (String s : lines) {
                        if (s.contains(theoryName)) {
                            s = s.replace(theoryName, newTheoryName);
                        }

                        result += s + "\n";
                    }

                    theory.delete();
                    writer.writeToFile(newTheoryPath, result);

                    return new File(newTheoryPath);
                }
            }

            return null;
        } catch (IOException e) {
            throw new IllegalArgumentException();
        }
    }
}
