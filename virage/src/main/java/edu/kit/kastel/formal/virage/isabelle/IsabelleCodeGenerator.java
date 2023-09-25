package edu.kit.kastel.formal.virage.isabelle;

import static edu.kit.kastel.formal.virage.isabelle.IsabelleCodeGenerationLanguage.Scala;

import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.io.StringWriter;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.text.SimpleDateFormat;
import java.util.Date;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.apache.commons.io.IOUtils;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import edu.kit.kastel.formal.util.ProcessUtils;
import edu.kit.kastel.formal.util.SimpleFileReader;
import edu.kit.kastel.formal.util.SimpleFileWriter;
import edu.kit.kastel.formal.util.StringUtils;
import edu.kit.kastel.formal.util.SystemUtils;
import edu.kit.kastel.formal.virage.core.ConfigReader;
import edu.kit.kastel.formal.virage.types.CodeGenerationFailedException;
import edu.kit.kastel.formal.virage.types.CompilationFailedException;
import edu.kit.kastel.formal.virage.types.CompositionProof;
import edu.kit.kastel.formal.virage.types.DecompositionTree;
import edu.kit.kastel.formal.virage.types.ExternalSoftwareUnavailableException;
import edu.kit.kastel.formal.virage.types.FrameworkRepresentation;
import edu.kit.kastel.formal.virage.types.IsabelleBuildFailedException;

/**
 * This class is used to engage the Isabelle Code Generation process and produce Scala code.
 *
 * @author VeriVote
 */
public final class IsabelleCodeGenerator {
    /**
     * File ending for template files.
     */
    public static final String DOT_TMPL = StringUtils.PERIOD + "template";

    /**
     * The logger.
     */
    private static final Logger LOGGER = LogManager.getLogger(IsabelleCodeGenerator.class);

    /**
     * Code suffix.
     */
    private static final String CODE = "_code";

    /**
     * End string.
     */
    private static final String END = "end";

    /**
     * File ending for Scala files.
     */
    private static final String DOT_SCALA =
            StringUtils.PERIOD + IsabelleCodeGenerationLanguage.Scala.name().toLowerCase();

    /**
     * File ending for jar files.
     */
    private static final String DOT_JAR = StringUtils.PERIOD + "jar";

    /**
     * String for code folder.
     */
    private static final String CODE_FOLDER = "code";

    /**
     * String for export file.
     */
    private static final String EXPORT_FILE = "export";

    /**
     * File name for the code root template.
     */
    private static final String CODE_ROOT_TEMPLATE_NAME = "code_root";

    /**
     * File name for the voting context template.
     */
    private static final String VOTING_CONTEXT_TEMPLATE_NAME = "voting_context";

    /**
     * The prefix for ad-hoc Isabelle sessions.
     */
    private static final String AD_HOC_SESSION_PREFIX = "ad_hoc_session_";

    /**
     * The pattern for simple date formats, intended for creating quasi unique file names.
     */
    private static final String DATE_FORMAT_PATTERN = "yyyyMMddHHmmss";

    /**
     * Module name variable.
     */
    private static final String MODULE_NAME_VAR = "$MODULE_NAME";

    /**
     * Language variable.
     */
    private static final String LANGUAGE_VAR = "$LANGUAGE";

    /**
     * Session name variable.
     */
    private static final String SESSION_NAME_VAR = "$SESSION_NAME";

    /**
     * Theory name variable.
     */
    private static final String THEORY_NAME_VAR = "$THEORY_NAME";

    /**
     * Parameter variable.
     */
    private static final String PARAM_VAR = "$PARAMS";

    /**
     * Parent name variable.
     */
    private static final String PARENT_NAME_VAR = "$PARENT_NAME";

    /**
     * Comment for enumerable.
     */
    private static final String ENUM_COMMENT = "ENUM";

    /**
     * HOL.equal.
     */
    private static final String EQUALITY =
            IsabelleUtils.HOL + IsabelleUtils.THEORY_NAME_SEPARATOR + "equal";

    /**
     * Equality comment.
     */
    private static final String EQUALITY_COMMENT = "EQUALITY";

    /**
     * Relation string.
     */
    private static final String RELATION =
            StringUtils.parenthesize2(
                    ScalaIsabelleFacade.DEFAULT_VARIABLE + StringUtils.COLON,
                    IsabelleUtils.SET + IsabelleUtils.THEORY_NAME_SEPARATOR + IsabelleUtils.SET_FUNC
                    + StringUtils.bracketize(
                            StringUtils.parenthesize(
                                    IsabelleUtils.DEFAULT_SET, IsabelleUtils.DEFAULT_SET)))
            + StringUtils.COLON;

    /**
     * Option1 comment.
     */
    private static final String OPTION1_COMMENT = "OPTION1";

    /**
     * Option2 comment.
     */
    private static final String OPTION2_COMMENT = "OPTION2";

    /**
     * String opening a Scala comment.
     */
    private static final String COMMENT_OPEN = "/* ";

    /**
     * String closing a Scala comment.
     */
    private static final String COMMENT_CLOSE = " */";

    /**
     * Bounded parameter name.
     */
    private static final String BOUNDED_PARAMETER = "bounded";

    /**
     * Eq parameter name.
     */
    private static final String EQ_PARAMETER = "eq";

    /**
     * File name for the scala file with the voting context.
     */
    private static final String VOTING_CONTEXT_SCALA_FILE_NAME = "votingContext";

    /**
     * Template for code export.
     */
    private static String exportTemplate = StringUtils.EMPTY;

    /**
     * Isabelle ROOT file template.
     */
    private static String rootTemplate = StringUtils.EMPTY;

    /**
     * Voting context template.
     */
    private static String votingContextTemplate = StringUtils.EMPTY;

    /**
     * The compositional framework.
     */
    private final FrameworkRepresentation framework;

    /**
     * The theory generator.
     */
    private final IsabelleTheoryGenerator generator;

    /**
     * The file reader.
     */
    private final SimpleFileReader reader;

    /**
     * Map of the code replacements.
     */
    private Map<String, String> codeReplacements;

    /**
     * Simple constructor that reads templates from resources.
     *
     * @param frameworkValue the framework representation to be used
     * @throws IOException if template reading fails
     */
    public IsabelleCodeGenerator(final FrameworkRepresentation frameworkValue) throws IOException {
        this.framework = frameworkValue;
        this.reader = new SimpleFileReader();
        this.generator = new IsabelleTheoryGenerator(frameworkValue);
        if (IsabelleCodeGenerator.exportTemplate == null
                || IsabelleCodeGenerator.exportTemplate.isEmpty()) {
            StringWriter writer = new StringWriter();
            final InputStream exportTemplateStream =
                    this.getClass().getClassLoader()
                    .getResourceAsStream(EXPORT_FILE + CODE + DOT_TMPL);
            try {
                IOUtils.copy(exportTemplateStream, writer, StandardCharsets.UTF_8);
            } catch (final IOException e) {
                LOGGER.error(e);
            }
            setExportTemplate(writer.toString());
            writer = new StringWriter();
            final InputStream rootTemplateStream = this.getClass().getClassLoader()
                    .getResourceAsStream(CODE_ROOT_TEMPLATE_NAME + DOT_TMPL);
            try {
                IOUtils.copy(rootTemplateStream, writer, StandardCharsets.UTF_8);
            } catch (final IOException e) {
                LOGGER.error(e);
            }
            setRootTemplate(writer.toString());

            writer = new StringWriter();
            final InputStream votingContextTemplateStream =
                    this.getClass().getClassLoader()
                    .getResourceAsStream(VOTING_CONTEXT_TEMPLATE_NAME + DOT_TMPL);
            try {
                IOUtils.copy(votingContextTemplateStream, writer, StandardCharsets.UTF_8);
            } catch (final IOException e) {
                LOGGER.error(e);
            }
            setVotingContextTemplate(writer.toString());
        }
        this.initCodeReplacements();
    }

    private static synchronized void setExportTemplate(final String newTemplate) {
        exportTemplate = newTemplate;
    }

    private static synchronized void setRootTemplate(final String newTemplate) {
        rootTemplate = newTemplate;
    }

    private static synchronized void setVotingContextTemplate(final String newTemplate) {
        votingContextTemplate = newTemplate;
    }

    private static String scalaCompileExec(final String isabelleExecutable,
                                           final String codeFilePath,
                                           final String votingContextPath,
                                           final String jarPath) {
        return StringUtils.printCollection2(
                isabelleExecutable, IsabelleProofChecker.SCALAC_TOOL, codeFilePath,
                votingContextPath, IsabelleProofChecker.INCL_SESS_DIR, jarPath);
    }

    private static String getCanonicalPath(final File file) throws CodeGenerationFailedException {
        final String filePath;
        try {
            filePath = file.getCanonicalPath();
        } catch (IOException e) {
            throw new CodeGenerationFailedException(e);
        }
        return filePath;
    }

    /**
     * Run terminating Scala compile process and log the output.
     *
     * @param codeFile the Scala code file
     * @param votingContext the voting context file
     * @param isaExec the executable Isabelle binary
     * @param jarPath the JAR path
     * @return the status value of the process result
     * @throws CodeGenerationFailedException in case of input, output or interruption failures
     */
    private static int runScalaCompileProcess(final File codeFile, final File votingContext,
                                              final String isaExec, final String jarPath)
                                                      throws CodeGenerationFailedException {
        final int status;
        try {
            status = ProcessUtils.runTerminatingProcessAndLogOutput(
                    scalaCompileExec(isaExec, getCanonicalPath(codeFile),
                                     getCanonicalPath(votingContext), jarPath));
        } catch (IOException | InterruptedException e) {
            throw new CodeGenerationFailedException(e);
        }
        return status;
    }

    private String prepareTheoryFile(final File theory, final String language) throws IOException {
        String originalName = StringUtils.EMPTY;
        String newName = StringUtils.EMPTY;
        final Map<String, String> map =
                IsabelleTheoryParser.getAllFunctionsAndDefinitions(theory.getCanonicalPath());
        if (map.keySet().size() != 1) {
            throw new IllegalArgumentException();
        }
        for (final String definition: map.keySet()) {
            originalName = definition;
            newName = definition + CODE;
        }
        final String originalDefinition =
                IsabelleTheoryParser.getDefinitionByName(originalName, theory);
        String newDefinition = originalDefinition.replaceAll(originalName, newName);
        for (final Map.Entry<String, String> oldEntry: this.codeReplacements.entrySet()) {
            // TODO: This is wrong if names are not prefix free.
            // This should be fixed if this solution stays permanently,
            // but it is only meant as a temporary fix anyway.
            newDefinition = newDefinition.replaceAll(oldEntry.getKey(), oldEntry.getValue());
        }
        final String exportCommand =
                IsabelleCodeGenerator.exportTemplate
                .replace(MODULE_NAME_VAR, newName).replace(LANGUAGE_VAR, language);
        final String result =
                newDefinition + System.lineSeparator() + System.lineSeparator() + exportCommand;
        final List<String> lines = this.reader.readFileByLine(theory);
        for (int i = 0; i < lines.size(); i++) {
            final String line = lines.get(i);
            if (StringUtils.removeWhitespace(line).equals(END)) {
                lines.add(i, result);
                break;
            }
        }
        final SimpleFileWriter writer = new SimpleFileWriter();
        writer.writeToFile(theory.getCanonicalPath(), lines);
        return newName;
    }

    /**
     * Prepare the theory file.
     *
     * @param theory the theory file
     * @param language the programming language for the generated code
     * @return the theory file name
     * @throws IOException in case of any input or output exceptions from file operations
     */
    public String prepareTheoryFile(final File theory,
                                    final IsabelleCodeGenerationLanguage language)
                                             throws IOException {
        return this.prepareTheoryFile(theory, language.toString());
    }

    private String buildSessionRoot(final String theoryName, final File theory) {
        // Session names MUST be universally unique, as Isabelle seems to be incapable
        // of rebuilding single sessions without triggering full rebuilds.
        // TODO: Is there a way to do it?
        final String sessionName = AD_HOC_SESSION_PREFIX
                + new SimpleDateFormat(DATE_FORMAT_PATTERN).format(new Date());
        String result =
                IsabelleCodeGenerator.rootTemplate
                .replace(SESSION_NAME_VAR, sessionName).replace(THEORY_NAME_VAR, theoryName);
        result = result.replace(PARENT_NAME_VAR, this.framework.getSessionName());
        final SimpleFileWriter writer = new SimpleFileWriter();
        writer.writeToFile(theory.getParent() + File.separator + IsabelleUtils.ROOT, result);
        return sessionName;
    }

    private File prepareVotingContext(final String theoryName, final String moduleName,
                                      final File moduleFile, final boolean setExplicitParameters)
                                              throws IOException {
        final File dir = moduleFile.getParentFile();
        final SimpleFileReader localReader = new SimpleFileReader();
        final String code = localReader.readFile(moduleFile);
        String result =
                IsabelleCodeGenerator.votingContextTemplate
                .replace(THEORY_NAME_VAR, theoryName).replace(MODULE_NAME_VAR, moduleName);
        final boolean containsEnum = code.contains(IsabelleUtils.ENUM);
        final boolean containsEquality = code.contains(EQUALITY);
        final boolean requiresRelation = code.contains(RELATION);
        final List<String> parameters = new LinkedList<String>();
        // Enable the required optional parts of the votingContextTemplate
        if (containsEnum) {
            result = result.replace(COMMENT_OPEN + ENUM_COMMENT, StringUtils.EMPTY)
                    .replace(ENUM_COMMENT + COMMENT_CLOSE, StringUtils.EMPTY);
            parameters.add(BOUNDED_PARAMETER);
        }
        if (containsEquality) {
            result = result.replace(COMMENT_OPEN + EQUALITY_COMMENT, StringUtils.EMPTY)
                    .replace(EQUALITY_COMMENT + COMMENT_CLOSE, StringUtils.EMPTY);
            parameters.add(StringUtils.prefixSpace(EQ_PARAMETER));
        }
        if (requiresRelation) {
            result = result.replace(COMMENT_OPEN + OPTION2_COMMENT, StringUtils.EMPTY)
                    .replace(OPTION2_COMMENT + COMMENT_CLOSE, StringUtils.EMPTY);
        } else {
            result = result.replace(COMMENT_OPEN + OPTION1_COMMENT, StringUtils.EMPTY)
                    .replace(OPTION1_COMMENT + COMMENT_CLOSE, StringUtils.EMPTY);
        }
        String paramString = StringUtils.EMPTY;
        // setExplicitParameters is required for now. Sometimes, Scala uses the implicit
        // values,
        // sometimes they have to be given explicitly, so we want to try both.
        if (!parameters.isEmpty() && setExplicitParameters) {
            paramString = StringUtils.parenthesize(StringUtils.printCollection(parameters));
        }
        result = result.replace(PARAM_VAR, paramString);
        final String path = dir + File.separator + VOTING_CONTEXT_SCALA_FILE_NAME + DOT_SCALA;
        final SimpleFileWriter writer = new SimpleFileWriter();
        writer.writeToFile(path, result);
        return SystemUtils.file(path);
    }

    /**
     * Prepare the voting context and wrap input or output failures into code generation failure.
     *
     * @param moduleName the name of the module
     * @param theoryName the name of the theory
     * @param codeFile the Scala code file
     * @param setExplicitParameters whether parameters should be set explicitly
     * @return the prepared voting context file
     * @throws CodeGenerationFailedException in case of input or output failures
     */
    private File generateVotingContextFile(final String theoryName,
                                           final String moduleName,
                                           final File codeFile,
                                           final boolean setExplicitParameters)
                                                   throws CodeGenerationFailedException {
        final File votingContext;
        try {
            votingContext = this.prepareVotingContext(theoryName, moduleName, codeFile,
                                                      setExplicitParameters);
        } catch (final IOException e) {
            throw new CodeGenerationFailedException(e);
        }
        return votingContext;
    }

    private void initCodeReplacements() throws IOException {
        final Map<String, String> replacements = new HashMap<String, String>();
        final Map<String, String> functionsAndDefinitions =
                IsabelleTheoryParser.getAllFunctionsAndDefinitions(this.framework.getTheoryPath());
        final Set<String> names = functionsAndDefinitions.keySet();
        for (final String name: names) {
            if (names.contains(name + CODE)) {
                replacements.put(name, name + CODE);
            }
        }
        this.codeReplacements = replacements;
    }

    private File invokeIsabelleCodeGeneration(final File theory, final String sessionName,
                                              final String theoryName)
                                                      throws IOException, InterruptedException,
                                                             IsabelleBuildFailedException,
                                                             ExternalSoftwareUnavailableException {
        final String generatedPath = theory.getParent();
        final String theoryPath = SystemUtils.file(this.framework.getTheoryPath()).getPath();
        final String isabelleCommand =
                StringUtils.printCollection2(
                        ConfigReader.getInstance().getIsabelleExecutable(),
                        IsabelleProofChecker.BUILD_TOOL, IsabelleProofChecker.EXPORT_FILES,
                        IsabelleProofChecker.INCL_SEL_SESS_DIR, generatedPath,
                        IsabelleProofChecker.INCL_SEL_SESS_DIR, theoryPath,
                        IsabelleProofChecker.SYS_OPT, IsabelleProofChecker.Q_AND_D_OPT,
                        IsabelleProofChecker.BUILD_OPT, sessionName);
        final int status = ProcessUtils.runTerminatingProcessAndLogOutput(isabelleCommand);
        if (status != 0) {
            LOGGER.error("Isabelle code generation failed.");
            throw new IsabelleBuildFailedException();
        }
        final String codePath =
                generatedPath + File.separator + EXPORT_FILE + File.separator
                + sessionName + IsabelleUtils.THEORY_NAME_SEPARATOR + theoryName + File.separator
                + CODE_FOLDER + File.separator;
        final File[] generatedFiles = SystemUtils.file(codePath).listFiles();
        // Delete ROOT file, it has served its purpose
        final File root = SystemUtils.file(generatedPath + File.separator + IsabelleUtils.ROOT);
        Files.delete(root.toPath());
        // Isabelle puts everything into one file when generating Scala or OCaml code
        return generatedFiles != null ? generatedFiles[0] : SystemUtils.file(codePath);
    }

    /**
     * Invoke Scala code file from the given Isabelle theory.
     *
     * @param theory the Isabelle theory file
     * @param sessionName the Isabelle session name
     * @param theoryName the Isabelle theory name
     * @return the Scala code file for the given Isabelle theory
     * @throws CodeGenerationFailedException in case of file operation failure or similar
     */
    private File invokeScalaCodeFromIsabelleTheory(final File theory, final String sessionName,
                                                   final String theoryName)
                                                           throws CodeGenerationFailedException {
        final File codeFile;
        try {
            codeFile = this.invokeIsabelleCodeGeneration(theory, sessionName, theoryName);
        } catch (IOException | InterruptedException | IsabelleBuildFailedException
                | ExternalSoftwareUnavailableException e) {
            throw new CodeGenerationFailedException(e);
        }
        return codeFile;
    }

    /**
     * Invokes Isabelle's code generator to generate code from a theory.
     *
     * @param theory the theory file
     * @param language the target language
     * @return a file containing the generated code
     * @throws CodeGenerationFailedException wrapping the actual cause
     */
    public File generateCode(final File theory, final IsabelleCodeGenerationLanguage language)
            throws CodeGenerationFailedException {
        // String moduleName = this.prepareTheoryFile(theory, language);
        final String theoryName =
                theory.getName().substring(0,
                        theory.getName().length() - (IsabelleUtils.DOT_THY.length()));
        final String sessionName = this.buildSessionRoot(theoryName, theory);
        try {
            final File codeFile;
            try {
                codeFile = this.invokeIsabelleCodeGeneration(theory, sessionName, theoryName);
            } catch (IOException | InterruptedException | ExternalSoftwareUnavailableException e) {
                throw new CodeGenerationFailedException(e);
            }
            return codeFile;
        } catch (final IsabelleBuildFailedException e) {
            throw new CodeGenerationFailedException(e);
        }
    }

    /**
     * Invokes Isabelle's code generator to create code from a composition.
     *
     * @param composition the composition
     * @param language the target language
     * @return a file containing the generated code
     * @throws CodeGenerationFailedException wrapping the actual cause
     */
    public File generateCode(final String composition,
                             final IsabelleCodeGenerationLanguage language)
                                     throws CodeGenerationFailedException {
        final File theory =
                this.generator.generateTheoryFile(composition, new LinkedList<CompositionProof>());
        return this.generateCode(theory, language);
    }

    /**
     * Invokes Isabelle's code generator to generate code from a composition.
     *
     * @param composition the composition
     * @param language the target language
     * @return a file containing the generated code
     * @throws CodeGenerationFailedException wrapping the actual cause
     */
    public File generateCode(final DecompositionTree composition,
                             final IsabelleCodeGenerationLanguage language)
                                     throws CodeGenerationFailedException {
        return this.generateCode(composition.toString(), language);
    }

    /**
     * Creates an ad-hoc Isabelle session, invokes code generation, attempts to compile the result
     * and returns an executable jar file if possible.
     *
     * @param theory the theory file, containing exactly one definition, on which code generation
     *      shall take place
     * @return an executable Scala-jar file if possible
     * @throws CodeGenerationFailedException wrapping the actual cause
     */
    public File generateScalaCodeAndCompile(final File theory)
            throws CodeGenerationFailedException {
        final String moduleName;
        try {
            moduleName = this.prepareTheoryFile(theory, Scala);
        } catch (final IOException e) {
            throw new CodeGenerationFailedException(e);
        }
        final String theoryName =
                theory.getName().substring(0,
                        theory.getName().length() - (IsabelleUtils.DOT_THY.length()));
        final String sessionName = this.buildSessionRoot(theoryName, theory);
        final File codeFile = invokeScalaCodeFromIsabelleTheory(theory, sessionName, theoryName);
        // First, try using implicit values only.
        final File cxtImplVals = generateVotingContextFile(theoryName, moduleName, codeFile, false);
        // If implicit values did not work, try setting them explicitly.
        final File cxtExplVals = generateVotingContextFile(theoryName, moduleName, codeFile, true);
        final String jarPath = codeFile.getParent() + File.separator + moduleName + DOT_JAR;
        final String isaExec;
        try {
            isaExec = ConfigReader.getInstance().getIsabelleExecutable();
        } catch (ExternalSoftwareUnavailableException e) {
            throw new CodeGenerationFailedException(e);
        }
        int status = 1;
        try {
            status = runScalaCompileProcess(codeFile, cxtImplVals, isaExec, jarPath);
        } catch (CodeGenerationFailedException e) {
            LOGGER.info("Scala compilation with implicit values did not work,"
                        + "now trying with explicit values.");
        }
        if (status != 0) {
            status = runScalaCompileProcess(codeFile, cxtExplVals, isaExec, jarPath);
            if (status != 0) {
                throw new CodeGenerationFailedException(
                        new CompilationFailedException(
                                "Generated Scala code could not be compiled."));
            }
        }
        LOGGER.info("Scala compilation was successful. The jar file can be found at " + jarPath);
        return SystemUtils.file(jarPath);
    }

    /**
     * Creates an ad-hoc Isabelle session, invokes code generation, attempts to compile the result
     * and returns an executable jar file if possible.
     *
     * @param composition the composition to be translated to Scala code
     * @return an executable Scala-jar file
     * @throws CodeGenerationFailedException wrapping the actual cause
     */
    public File generateScalaCodeAndCompile(final String composition)
            throws CodeGenerationFailedException {
        final File theory =
                this.generator.generateTheoryFile(composition, new LinkedList<CompositionProof>());
        try {
            return this.generateScalaCodeAndCompile(theory);
        } catch (final CodeGenerationFailedException e) {
            throw new CodeGenerationFailedException(e);
        }
    }
}
