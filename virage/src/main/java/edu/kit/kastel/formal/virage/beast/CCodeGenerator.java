package edu.kit.kastel.formal.virage.beast;

import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.io.StringWriter;
import java.nio.charset.StandardCharsets;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.apache.commons.io.IOUtils;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import edu.kit.kastel.formal.util.Pair;
import edu.kit.kastel.formal.util.SimpleFileWriter;
import edu.kit.kastel.formal.util.StringUtils;
import edu.kit.kastel.formal.util.SystemUtils;
import edu.kit.kastel.formal.virage.core.ConfigReader;
import edu.kit.kastel.formal.virage.isabelle.IsabelleCodeGenerator;
import edu.kit.kastel.formal.virage.isabelle.IsabelleTheoryGenerator;
import edu.kit.kastel.formal.virage.prolog.PrologPredicate;
import edu.kit.kastel.formal.virage.types.Component;
import edu.kit.kastel.formal.virage.types.DecompositionTree;
import edu.kit.kastel.formal.virage.types.FrameworkRepresentation;

/**
 * Generator to create C code from compositions.
 *
 * @author VeriVote
 */
public final class CCodeGenerator {
    /**
     * The logger.
     */
    private static final Logger LOGGER = LogManager.getRootLogger();

    /**
     * String representation for the C header file ending.
     */
    private static final String DOT_H = StringUtils.PERIOD + "h";

    /**
     * String representation for the C file ending.
     */
    private static final String DOT_C = StringUtils.PERIOD + "c";

    /**
     * Name of the directory with the target sources.
     */
    private static final String TARGET_DIR = "target" + File.separator + "generated-sources";

    /**
     * Name of the directory to the C implementations.
     */
    private static final String C_DIR = "c_implementations";

    /**
     * File name for the voting rule file.
     */
    private static final String RULE_FILE = "voting_rule";

    /**
     * File name for the code file template.
     */
    private static final String CODE_FILE_TEMPLATE_NAME = "code_file";

    /**
     * File name for the components file template.
     */
    private static final String COMPONENTS_FILE_TEMPLATE_NAME = "components";

    /**
     * Variable for code content to replace from the template file.
     */
    private static final String CODE_CONTENT_VARIABLE = "$CONTENT";

    /**
     * Variable for file content entry to replace from the template file.
     */
    private static final String FILE_CONTENT_ENTRY_VARIABLE = "$ENTRY";

    /**
     * Variable for component index to replace from the template file.
     */
    private static final String COMPONENT_INDEX_VARIABLE = "$IDX";

    /**
     * Variable for component parameter to replace from the template file.
     */
    private static final String COMPONENT_PARAMETER_VARIABLE = "$PARAM_";

    /**
     * Template for the voting_rule.c file.
     */
    private final String codeFileTemplate;

    /**
     * Templates for each component.
     */
    private final Map<String, String> templates;

    /**
     * Signatures of each component.
     */
    private final Map<String, List<String>> signatures;

    /**
     * The framework.
     */
    private final FrameworkRepresentation frameworkField;

    /**
     * Simple constructor.
     * @param framework the framework.
     */
    public CCodeGenerator(final FrameworkRepresentation framework) {
        this.frameworkField = framework;
        final StringWriter writer = new StringWriter();
        final InputStream codeFileTemplateStream =
                this.getClass().getClassLoader()
                .getResourceAsStream(CODE_FILE_TEMPLATE_NAME + IsabelleCodeGenerator.DOT_TMPL);
        try {
            IOUtils.copy(codeFileTemplateStream, writer, StandardCharsets.UTF_8);
        } catch (final IOException e) {
            e.printStackTrace();
        }
        this.codeFileTemplate = writer.toString();
        final InputStream compositionsTemplateStream =
                this.getClass().getClassLoader()
                .getResourceAsStream(C_DIR + File.separator + COMPONENTS_FILE_TEMPLATE_NAME
                                        + IsabelleCodeGenerator.DOT_TMPL);
        try {
            IOUtils.copy(compositionsTemplateStream, writer, StandardCharsets.UTF_8);
        } catch (final IOException e) {
            e.printStackTrace();
        }
        this.templates = new HashMap<String, String>();
        this.signatures = new HashMap<String, List<String>>();
        final String componentNameGroup = "componentName";
        final String implementationGroup = "implementation";
        final String signatureGroup = "signature";
        final Pattern pattern = Pattern.compile("\\/\\/[ ]*(?<" + componentNameGroup
                + ">\\w+)\n(?<" + implementationGroup + ">[^\\(]*(?<"
                + signatureGroup + ">[^\\)]*\\)).*)\\/\\/[ ]*\\k<" + componentNameGroup + ">"
                + System.lineSeparator(),
                Pattern.DOTALL);
        final Matcher matcher = pattern.matcher(writer.toString());
        while (matcher.find()) {
            this.templates.put(matcher.group(componentNameGroup),
                    matcher.group(implementationGroup));
            String rawSignature = matcher.group(signatureGroup);
            // Remove brackets.
            rawSignature = rawSignature.substring(0, rawSignature.length() - 1);
            final List<String> parameterNames = new LinkedList<String>();
            final String[] parameters = rawSignature.split(StringUtils.COMMA);
            for (int i = 0; i < parameters.length; i++) {
                parameters[i] = parameters[i].strip();
                final String[] parameterNameArray = parameters[i].split(StringUtils.SPACE);
                // Correct name is the last entry, as all trailing whitespace was removed.
                final String parameterName = parameterNameArray[parameterNameArray.length - 1];
                parameterNames.add(parameterName);
            }
            this.signatures.put(matcher.group(componentNameGroup), parameterNames);
        }
        this.copyImplementationResources();
    }

    /**
     * Creates C code from a composition.
     * @param compositionString the composition
     * @return a C file containing an implementation of the composition
     */
    public File getCCodeFromComposition(final String compositionString) {
        final DecompositionTree composition = DecompositionTree.parseString(compositionString);
        final List<String> missingTemplates = this.findMissingTemplates(composition);
        for (final String missingTemplate: missingTemplates) {
            LOGGER.warn("Template missing for component: " + missingTemplate);
        }
        final Pair<Pair<String, String>, Integer> res =
                this.getCCodeFromComposition(composition, 0);
        String fileContents =
                this.codeFileTemplate.replace(CODE_CONTENT_VARIABLE,
                                              res.getFirstValue().getSecondValue());
        fileContents = fileContents.replace(FILE_CONTENT_ENTRY_VARIABLE,
                                            res.getFirstValue().getFirstValue()
                                            + this.buildParameterString(composition.getLabel()));
        final File result =
                SystemUtils.file(TARGET_DIR + File.separator + RULE_FILE
                                + System.currentTimeMillis() + DOT_C);
        (new SimpleFileWriter()).writeToFile(result.getAbsolutePath(), fileContents);
        return result;
    }

    private Pair<Pair<String, String>, Integer> getCCodeFromComposition(
            final DecompositionTree composition, final int ctr) {
        String head = StringUtils.EMPTY;
        String body = StringUtils.EMPTY;
        final Component currentComponent =
                this.frameworkField.getComponent(composition.getLabel());
        if (currentComponent != null) {
            final String componentName = composition.getLabel();
            String componentTemplate = this.templates.get(componentName);
            if (componentTemplate != null) {
                componentTemplate =
                        componentTemplate.replace(COMPONENT_INDEX_VARIABLE, String.valueOf(ctr));
                int moduleCounter = 1;
                for (int i = 0; i < composition.getArity(); i++) {
                    final DecompositionTree child = composition.getChildren().get(i);
                    final String replacement;
                    if (PrologPredicate.isVariable(child.getLabel())) {
                        replacement = "DEFAULT_" + currentComponent.getParameters()
                            .get(i).toString().toUpperCase();
                    } else {
                        final Pair<Pair<String, String>, Integer> childCode = this
                                .getCCodeFromComposition(child, ctr + 1);
                        body += childCode.getFirstValue().getSecondValue() + System.lineSeparator();
                        replacement = childCode.getFirstValue().getFirstValue()
                                + this.buildParameterString(child.getLabel());
                    }
                    componentTemplate = componentTemplate
                            .replace(COMPONENT_PARAMETER_VARIABLE + String.valueOf(moduleCounter),
                                     replacement);
                    moduleCounter++;
                }
                body += componentTemplate;
                head = componentName + IsabelleTheoryGenerator.NAME_SEPARATOR + String.valueOf(ctr);
            }
        }
        if (currentComponent == null || !this.templates.containsKey(currentComponent.getName())) {
            head = composition.getLabel();
        }
        return new Pair<Pair<String, String>, Integer>(new Pair<String, String>(head, body), ctr);
    }

    private String buildParameterString(final String name) {
        if (!this.signatures.containsKey(name)) {
            return StringUtils.EMPTY;
        }
        return StringUtils.parenthesize(StringUtils.printCollection(this.signatures.get(name)));
    }

    private List<String> findMissingTemplates(final DecompositionTree composition) {
        return this.findMissingTemplates(composition, new LinkedList<String>());
    }

    private List<String> findMissingTemplates(final DecompositionTree composition,
                                              final List<String> found) {
        if (!this.templates.containsKey(composition.getLabel())) {
            found.add(composition.getLabel());
        }
        for (final DecompositionTree child: composition.getChildren()) {
            this.findMissingTemplates(child, found);
        }
        return found;
    }

    /*public File generateAndCompileCCodeFromComposition(final String compositionString,
                                                         final int numVoters,
                                                         final int numAlternatives)
                throws IOException, InterruptedException, CompilationFailedException {
        final File votingRuleFile = this.getCCodeFromComposition(compositionString);
        String cFiles = StringUtils.EMPTY;
        String resourceLocation = StringUtils.EMPTY;
        for (final String s: additionalFiles) {
            final String location = C_DIR + File.separator + s;
            cFiles += StringUtils.prefixSpace(this.getClass().getClassLoader()
                .getResource(location).getFile());
            if (resourceLocation.isEmpty()) {
                resourceLocation = new File(this.getClass().getClassLoader()
                    .getResource(location).getFile()).getParent();
            }
        }
        final File tmpVotingRuleFile = new File(resourceLocation
            + File.separator + "tmp_" + RULE_FILE + DOT_C);
        if (tmpVotingRuleFile.exists()) {
            tmpVotingRuleFile.delete();
        }
        Files.copy(votingRuleFile.toPath(), tmpVotingRuleFile.toPath());
        final File exeFile =
            new File(TARGET_DIR + File.separator + RULE_FILE + StringUtils.PERIOD
                        + ScalaIsabelleFacade.DEFAULT_VARIABLE).getAbsoluteFile();
        final String gccCommand = ConfigReader.getInstance().getGccExecutable()
                + StringUtils.prefixSpace(tmpVotingRuleFile.getAbsolutePath())
                + cFiles + " -o " + exeFile.getAbsolutePath() + " -D V=" + numVoters
                + " -D C=" + numAlternatives;
        final Pair<String, String> output = ProcessUtils.runTerminatingProcess(gccCommand);
        if (!output.getFirstValue().isEmpty()) {
            LOGGER.warn(output.getFirstValue());
        }
        if (!output.getSecondValue().isEmpty()) {
            LOGGER.error(output.getSecondValue());
            throw new CompilationFailedException("Compilation failed,
                invoked as follows: " + gccCommand);
        }
        return exeFile;
    }*/

    private void copyImplementationResources() {
        final String typesFile = "types";
        final String wrapperFile = "wrapper";
        SystemUtils.copyResourceToFile(C_DIR + File.separator + typesFile + DOT_C,
                ConfigReader.getInstance().getDefaultOutputPath() + File.separator
                + typesFile + DOT_C);
        SystemUtils.copyResourceToFile(C_DIR + File.separator + typesFile + DOT_H,
                ConfigReader.getInstance().getDefaultOutputPath() + File.separator
                + typesFile + DOT_H);
        SystemUtils.copyResourceToFile(C_DIR + File.separator + RULE_FILE + DOT_H,
                ConfigReader.getInstance().getDefaultOutputPath()
                + File.separator + RULE_FILE + DOT_C);
        SystemUtils.copyResourceToFile(C_DIR + File.separator + wrapperFile + DOT_C,
                ConfigReader.getInstance().getDefaultOutputPath() + File.separator
                + wrapperFile + DOT_C);
    }
}
