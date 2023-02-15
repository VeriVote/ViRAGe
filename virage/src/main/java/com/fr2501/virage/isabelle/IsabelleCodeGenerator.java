package com.fr2501.virage.isabelle;

import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.io.StringWriter;
import java.nio.charset.StandardCharsets;
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

import com.fr2501.util.ProcessUtils;
import com.fr2501.util.SimpleFileReader;
import com.fr2501.util.SimpleFileWriter;
import com.fr2501.util.StringUtils;
import com.fr2501.virage.core.ConfigReader;
import com.fr2501.virage.types.CodeGenerationFailedException;
import com.fr2501.virage.types.CompilationFailedException;
import com.fr2501.virage.types.CompositionProof;
import com.fr2501.virage.types.DecompositionTree;
import com.fr2501.virage.types.ExternalSoftwareUnavailableException;
import com.fr2501.virage.types.FrameworkRepresentation;
import com.fr2501.virage.types.IsabelleBuildFailedException;

/**
 * This class is used to engage the Isabelle Code Generation process and produce Scala code.
 *
 * @author VeriVote
 */
public final class IsabelleCodeGenerator {
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
     * Template for code export.
     */
    private static String exportTemplate = "";
    /**
     * Isabelle ROOT file template.
     */
    private static String rootTemplate = "";
    /**
     * Voting context template.
     */
    private static String votingContextTemplate = "";
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
     * Enum string.
     */
    private static final String ENUM = "Enum";
    /**
     * Enum comment.
     */
    private static final String ENUM_COMMENT = "ENUM";
    /**
     * HOL.equal.
     */
    private static final String EQUALITY = "HOL.equal";
    /**
     * Equality comment.
     */
    private static final String EQUALITY_COMMENT = "EQUALITY";
    /**
     * Relation string.
     */
    private static final String RELATION = "(x: Set.set[(A, A)]):";
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
    private static final String SCALA_COMMENT_OPEN = "/* ";

    /**
     * String closing a Scala comment.
     */
    private static final String SCALA_COMMENT_CLOSE = " */";

    /**
     * The compositional framework.
     */
    private final FrameworkRepresentation framework;

    /**
     * The theory generator.
     */
    private final IsabelleTheoryGenerator generator;
    /**
     * The Isabelle theory parser.
     */
    private final IsabelleTheoryParser parser;
    /**
     * The file reader.
     */
    private final SimpleFileReader reader;

    /**
     * Map of the code replacemenents.
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
        this.parser = new IsabelleTheoryParser();
        this.generator = new IsabelleTheoryGenerator(frameworkValue);

        if (exportTemplate.isEmpty()) {
            StringWriter writer = new StringWriter();

            final InputStream exportTemplateStream = this.getClass().getClassLoader()
                    .getResourceAsStream("export_code.template");
            try {
                IOUtils.copy(exportTemplateStream, writer, StandardCharsets.UTF_8);
            } catch (final IOException e) {
                LOGGER.error(e);
            }
            exportTemplate = writer.toString();

            writer = new StringWriter();
            final InputStream rootTemplateStream = this.getClass().getClassLoader()
                    .getResourceAsStream("code_root.template");
            try {
                IOUtils.copy(rootTemplateStream, writer, StandardCharsets.UTF_8);
            } catch (final IOException e) {
                LOGGER.error(e);
            }
            rootTemplate = writer.toString();

            writer = new StringWriter();
            final InputStream votingContextTemplateStream = this.getClass().getClassLoader()
                    .getResourceAsStream("voting_context.template");
            try {
                IOUtils.copy(votingContextTemplateStream, writer, StandardCharsets.UTF_8);
            } catch (final IOException e) {
                LOGGER.error(e);
            }
            votingContextTemplate = writer.toString();
        }

        this.initCodeReplacements();
    }

    private String buildSessionRoot(final String theoryName, final File theory) {
        // Session names MUST be universally unique, as Isabelle seems to be incapable
        // of
        // rebuilding single sessions without triggering full rebuilds.
        // TODO: Is there a way to do it?
        final String sessionName = "ad_hoc_session_"
                + new SimpleDateFormat("yyyyMMddHHmmss").format(new Date());

        String result = rootTemplate.replace(SESSION_NAME_VAR, sessionName).replace(THEORY_NAME_VAR,
                theoryName);
        result = result.replace(PARENT_NAME_VAR, this.framework.getSessionName());
        final SimpleFileWriter writer = new SimpleFileWriter();
        writer.writeToFile(theory.getParent() + File.separator + IsabelleUtils.ROOT, result);

        return sessionName;
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
            final IsabelleCodeGenerationLanguage language) throws CodeGenerationFailedException {
        return this.generateCode(composition.toString(), language);
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

        final String theoryName = theory.getName().substring(0,
                theory.getName().length() - (IsabelleUtils.FILE_EXTENSION.length()));

        final String sessionName = this.buildSessionRoot(theoryName, theory);

        try {
            final File codeFile;
            try {
                codeFile = this.invokeIsabelleCodeGeneration(theory, sessionName,
                        theoryName);
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
            final IsabelleCodeGenerationLanguage language) throws CodeGenerationFailedException {
        final File theory = this.generator.generateTheoryFile(composition,
                new LinkedList<CompositionProof>());

        return this.generateCode(theory, language);
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
            moduleName = this.prepareTheoryFile(theory, "Scala");
        } catch (final IOException e) {
            throw new CodeGenerationFailedException(e);
        }

        final String theoryName = theory.getName().substring(0,
                theory.getName().length() - (IsabelleUtils.FILE_EXTENSION.length()));

        final String sessionName = this.buildSessionRoot(theoryName, theory);

        final File codeFile;
        try {
            codeFile = this.invokeIsabelleCodeGeneration(theory, sessionName, theoryName);
        } catch (IOException | InterruptedException | IsabelleBuildFailedException
                | ExternalSoftwareUnavailableException e) {
            throw new CodeGenerationFailedException(e);
        }

        // First, try using implicit values only
        File votingContext;
        try {
            votingContext = this.prepareVotingContext(theoryName, moduleName, codeFile, false);
        } catch (final IOException e) {
            throw new CodeGenerationFailedException(e);
        }

        final String jarPath = codeFile.getParent() + File.separator + moduleName + ".jar";

        int status;
        final String outputParameter = " -d ";
        final String scalacCommand = " scalac ";
        try {
            status = ProcessUtils.runTerminatingProcessAndLogOutput(
                    ConfigReader.getInstance().getIsabelleExecutable() + scalacCommand
                            + codeFile.getCanonicalPath() + StringUtils.SPACE
                            + votingContext.getCanonicalPath()
                            + outputParameter + jarPath);
        } catch (IOException | InterruptedException | ExternalSoftwareUnavailableException e) {
            throw new CodeGenerationFailedException(e);
        }

        if (status != 0) {
            // Implicit values did not work, try setting them explicitly.
            try {
                votingContext = this.prepareVotingContext(theoryName, moduleName, codeFile, true);
            } catch (final IOException e) {
                throw new CodeGenerationFailedException(e);
            }

            try {
                status = ProcessUtils.runTerminatingProcessAndLogOutput(
                        ConfigReader.getInstance().getIsabelleExecutable() + scalacCommand
                                + codeFile.getCanonicalPath() + StringUtils.SPACE
                                + votingContext.getCanonicalPath()
                                + outputParameter + jarPath);
            } catch (IOException | InterruptedException | ExternalSoftwareUnavailableException e) {
                throw new CodeGenerationFailedException(e);
            }

            if (status != 0) {
                throw new CodeGenerationFailedException(
                        new CompilationFailedException(
                                "Generated Scala code could not be compiled."));
            }
        }

        LOGGER.info("Scala compilation was successful. The jar file can be found at " + jarPath);

        return new File(jarPath);
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
        final File theory = this.generator.generateTheoryFile(composition,
                new LinkedList<CompositionProof>());

        try {
            return this.generateScalaCodeAndCompile(theory);
        } catch (final CodeGenerationFailedException e) {
            throw new CodeGenerationFailedException(e);
        }
    }

    private void initCodeReplacements() throws IOException {
        final Map<String, String> replacements = new HashMap<String, String>();
        final Map<String, String> functionsAndDefinitions = this.parser
                .getAllFunctionsAndDefinitions(this.framework.getTheoryPath());

        final Set<String> names = functionsAndDefinitions.keySet();

        for (final String name : names) {
            if (names.contains(name + CODE)) {
                replacements.put(name, name + CODE);
            }
        }

        this.codeReplacements = replacements;
    }

    private File invokeIsabelleCodeGeneration(final File theory, final String sessionName,
            final String theoryName) throws IOException, InterruptedException,
        IsabelleBuildFailedException, ExternalSoftwareUnavailableException {
        final String generatedPath = theory.getParent();
        final String theoryPath = new File(this.framework.getTheoryPath()).getCanonicalPath();

        final String isabelleCommand = ConfigReader.getInstance().getIsabelleExecutable()
                + " build -e -D " + generatedPath + " -D " + theoryPath + " -o quick_and_dirty -b "
                + sessionName;

        final int status = ProcessUtils.runTerminatingProcessAndLogOutput(isabelleCommand);

        if (status != 0) {
            LOGGER.error("Isabelle code generation failed.");

            throw new IsabelleBuildFailedException();
        }

        final String codePath = generatedPath + File.separator + "export" + File.separator
                + sessionName + "." + theoryName + File.separator + "code" + File.separator;
        final File codeDir = new File(codePath);
        final File[] generatedFiles = codeDir.listFiles();

        // Delete ROOT file, it has served its purpose
        final File root = new File(generatedPath + File.separator + IsabelleUtils.ROOT);
        root.delete();

        // Isabelle puts everything into one file when generating Scala and OCaml code
        return generatedFiles[0];
    }

    // TODO Should this become public?
    @SuppressWarnings("unused")
    private String prepareTheoryFile(final File theory,
            final IsabelleCodeGenerationLanguage language) throws IOException {
        return this.prepareTheoryFile(theory, language.toString());
    }

    private String prepareTheoryFile(final File theory, final String language) throws IOException {
        String originalName = "";
        String newName = "";

        final Map<String, String> map = this.parser
                .getAllFunctionsAndDefinitions(theory.getCanonicalPath());
        if (map.keySet().size() != 1) {
            throw new IllegalArgumentException();
        }

        for (final String definition : map.keySet()) {
            originalName = definition;
            newName = definition + CODE;
        }

        final String originalDefinition = this.parser.getDefinitionByName(originalName, theory);

        String newDefinition = originalDefinition.replaceAll(originalName, newName);

        for (final String old : this.codeReplacements.keySet()) {
            // TODO: This is wrong if names are not prefix free.
            // This should be fixed if this solution stays permanently,
            // but it is only meant as a temporary fix anyway.
            newDefinition = newDefinition.replaceAll(old, this.codeReplacements.get(old));
        }

        String exportCommand = exportTemplate.replace(MODULE_NAME_VAR, newName);
        exportCommand = exportCommand.replace(LANGUAGE_VAR, language);

        final String result = newDefinition + "\n\n" + exportCommand;

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

    private File prepareVotingContext(final String theoryName, final String moduleName,
            final File moduleFile, final boolean setExplicitParameters) throws IOException {
        final File dir = moduleFile.getParentFile();

        final SimpleFileReader localReader = new SimpleFileReader();
        final String code = localReader.readFile(moduleFile);

        String result = votingContextTemplate.replace(THEORY_NAME_VAR, theoryName)
                .replace(MODULE_NAME_VAR, moduleName);

        final boolean containsEnum = code.contains(ENUM);
        final boolean containsEquality = code.contains(EQUALITY);
        final boolean requiresRelation = code.contains(RELATION);

        final List<String> parameters = new LinkedList<String>();

        // Enable the required optional parts of the votingContextTemplate
        if (containsEnum) {
            result = result.replace(SCALA_COMMENT_OPEN + ENUM_COMMENT, "")
                    .replace(ENUM_COMMENT + SCALA_COMMENT_CLOSE, "");
            parameters.add("bounded");
        }

        if (containsEquality) {
            result = result.replace(SCALA_COMMENT_OPEN + EQUALITY_COMMENT, "")
                    .replace(EQUALITY_COMMENT + SCALA_COMMENT_CLOSE,
                    "");
            parameters.add("eq");
        }

        if (requiresRelation) {
            result = result.replace(SCALA_COMMENT_OPEN + OPTION2_COMMENT, "")
                    .replace(OPTION2_COMMENT + SCALA_COMMENT_CLOSE,
                    "");
        } else {
            result = result.replace(SCALA_COMMENT_OPEN + OPTION1_COMMENT, "")
                    .replace(OPTION1_COMMENT + SCALA_COMMENT_CLOSE,
                    "");
        }

        String paramString = "";
        // setExplicitParameters is required for now. Sometimes, Scala uses the implicit
        // values,
        // sometimes they have to be given explicitly, so we want to try both.
        if (!parameters.isEmpty() && setExplicitParameters) {
            paramString = "(" + StringUtils.printCollection(parameters) + ")";
        }
        result = result.replace(PARAM_VAR, paramString);

        final String path = dir.getCanonicalPath() + File.separator + "votingContext.scala";

        final SimpleFileWriter writer = new SimpleFileWriter();
        writer.writeToFile(path, result);

        return new File(path);
    }
}
