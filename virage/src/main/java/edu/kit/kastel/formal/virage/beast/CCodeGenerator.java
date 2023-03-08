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
     * Template for the voting_rule.c file.
     */
    private final String codeFileTemplate;
    /**
     * Templates for the components of the framework.
     */
    private final String compositionsTemplate;
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
        final InputStream codeFileTemplateStream = this.getClass().getClassLoader()
                .getResourceAsStream("code_file.template");
        try {
            IOUtils.copy(codeFileTemplateStream, writer, StandardCharsets.UTF_8);
        } catch (final IOException e) {
            e.printStackTrace();
        }

        this.codeFileTemplate = writer.toString();

        final InputStream compositionsTemplateStream = this.getClass().getClassLoader()
                .getResourceAsStream("c_implementations/components.template");
        try {
            IOUtils.copy(compositionsTemplateStream, writer, StandardCharsets.UTF_8);
        } catch (final IOException e) {
            e.printStackTrace();
        }

        this.compositionsTemplate = writer.toString();

        this.templates = new HashMap<String, String>();
        this.signatures = new HashMap<String, List<String>>();

        final String componentNameGroup = "componentName";
        final String implementationGroup = "implementation";
        final String signatureGroup = "signature";
        final Pattern pattern = Pattern.compile("\\/\\/[ ]*(?<" + componentNameGroup
                + ">\\w+)\n(?<" + implementationGroup + ">[^\\(]*(?<"
                + signatureGroup + ">[^\\)]*\\)).*)\\/\\/[ ]*\\k<" + componentNameGroup + ">\n",
                Pattern.DOTALL);
        final Matcher matcher = pattern.matcher(this.compositionsTemplate);

        while(matcher.find()) {
            this.templates.put(matcher.group(componentNameGroup),
                    matcher.group(implementationGroup));

            String rawSignature = matcher.group(signatureGroup);

            // Remove brackets.
            rawSignature = rawSignature.substring(0, rawSignature.length() - 1);

            final List<String> parameterNames = new LinkedList<String>();
            final String[] parameters = rawSignature.split(",");
            for(int i = 0; i < parameters.length; i++) {
                parameters[i] = parameters[i].strip();

                final String[] parameterNameArray = parameters[i].split(" ");
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
     * @return a .c file containing an implementation of the composition
     */
    public File getCCodeFromComposition(final String compositionString) {
        final DecompositionTree composition = DecompositionTree.parseString(compositionString);

        final List<String> missingTemplates = this.findMissingTemplates(composition);

        for(final String missingTemplate : missingTemplates) {
            LOGGER.warn("Template missing for component: " + missingTemplate);
        }

        final Pair<Pair<String, String>, Integer> res = this.getCCodeFromComposition(composition,
                0);

        String fileContents = this.codeFileTemplate.replace("$CONTENT",
                res.getFirstValue().getSecondValue());
        fileContents = fileContents.replace("$ENTRY", res.getFirstValue().getFirstValue()
                + this.buildParameterString(composition.getLabel()));

        final File result = new File("target/generated-sources/voting_rule"
                + System.currentTimeMillis() + ".c");
        (new SimpleFileWriter()).writeToFile(result.getAbsolutePath(), fileContents);

        return result;
    }

    private Pair<Pair<String, String>, Integer> getCCodeFromComposition(
            final DecompositionTree composition, final int ctr) {
        String head = "";
        String body = "";

        final Component currentComponent = this.frameworkField
                .getComponent(composition.getLabel());
        if (currentComponent != null) {
            final String componentName = composition.getLabel();

            if (this.templates.containsKey(componentName)) {
                String componentTemplate = this.templates.get(componentName);

                componentTemplate = componentTemplate.replace("$IDX", String.valueOf(ctr));

                int moduleCounter = 1;
                for (int i = 0; i < composition.getArity(); i++) {
                    final DecompositionTree child = composition.getChildren().get(i);

                    final String replacement;
                    if(PrologPredicate.isVariable(child.getLabel())) {
                        replacement = "DEFAULT_" + currentComponent.getParameters()
                            .get(i).toString().toUpperCase();
                    } else {
                        final Pair<Pair<String, String>, Integer> childCode = this
                                .getCCodeFromComposition(child, ctr + 1);

                        body += childCode.getFirstValue().getSecondValue() + System.lineSeparator();
                        replacement = childCode.getFirstValue().getFirstValue()
                                + this.buildParameterString(child.getLabel());
                    }

                    componentTemplate = componentTemplate.replace(
                            "$PARAM_" + String.valueOf(moduleCounter),
                            replacement);
                    moduleCounter++;
                }

                body += componentTemplate;
                head = componentName + "_" + String.valueOf(ctr);
            }
        }

        if (currentComponent == null || !this.templates.containsKey(currentComponent.getName())) {
            head = composition.getLabel();
        }

        return new Pair<Pair<String, String>, Integer>(new Pair<String, String>(head, body), ctr);
    }

    private String buildParameterString(final String name) {
        if(!this.signatures.containsKey(name)) {
            return "";
        }

        return StringUtils.parenthesize(StringUtils.printCollection(this.signatures.get(name)));
    }

    private List<String> findMissingTemplates(final DecompositionTree composition) {
        return this.findMissingTemplates(composition, new LinkedList<String>());
    }

    private List<String> findMissingTemplates(final DecompositionTree composition,
            final List<String> found) {
        if(!this.templates.keySet().contains(composition.getLabel())) {
            found.add(composition.getLabel());
        }

        for(final DecompositionTree child : composition.getChildren()) {
            this.findMissingTemplates(child, found);
        }

        return found;
    }

    /*public File generateAndCompileCCodeFromComposition(final String compositionString,
            final int numVoters, final int numCandidates) throws IOException,
                InterruptedException, CompilationFailedException {
        final File votingRuleFile = this.getCCodeFromComposition(compositionString);

        String cFiles = "";
        String resourceLocation = "";
        for(final String s : additionalFiles) {
            final String location = "c_implementations" + File.separator + s;

            cFiles += StringUtils.SPACE + this.getClass().getClassLoader()
                .getResource(location).getFile();

            if(resourceLocation.isEmpty()) {
                resourceLocation = new File(this.getClass().getClassLoader()
                    .getResource(location).getFile()).getParent();
            }
        }

        final File tmpVotingRuleFile = new File(resourceLocation
            + File.separator + "tmp_voting_rule.c");
        if(tmpVotingRuleFile.exists()) {
            tmpVotingRuleFile.delete();
        }
        Files.copy(votingRuleFile.toPath(), tmpVotingRuleFile.toPath());

        final File exeFile = new File("target/generated_sources/voting_rule.x").getAbsoluteFile();
        final String gccCommand = ConfigReader.getInstance().getGccExecutable()
                + StringUtils.SPACE + tmpVotingRuleFile.getAbsolutePath()
                + cFiles + " -o " + exeFile.getAbsolutePath() + " -D V=" + numVoters
                + " -D C=" + numCandidates;

        final Pair<String, String> output = ProcessUtils.runTerminatingProcess(gccCommand);
        if(!output.getFirstValue().isEmpty()) {
            LOGGER.warn(output.getFirstValue());
        }

        if(!output.getSecondValue().isEmpty()) {
            LOGGER.error(output.getSecondValue());

            throw new CompilationFailedException("Compilation failed,
                invoked as follows: " + gccCommand);
        }

        return exeFile;
    }*/

    private void copyImplementationResources() {
        SystemUtils.copyResourceToFile("c_implementations/types.c",
                ConfigReader.getInstance().getDefaultOutputPath() + File.separator + "types.c");
        SystemUtils.copyResourceToFile("c_implementations/types.h",
                ConfigReader.getInstance().getDefaultOutputPath() + File.separator + "types.h");
        SystemUtils.copyResourceToFile("c_implementations/voting_rule.h",
                ConfigReader.getInstance().getDefaultOutputPath()
                + File.separator + "voting_rule.c");
        SystemUtils.copyResourceToFile("c_implementations/wrapper.c",
                ConfigReader.getInstance().getDefaultOutputPath() + File.separator + "wrapper.c");
    }

}
