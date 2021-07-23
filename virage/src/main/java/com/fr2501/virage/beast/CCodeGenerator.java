package com.fr2501.virage.beast;

import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.io.StringWriter;
import java.nio.charset.StandardCharsets;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.apache.commons.io.IOUtils;

import com.fr2501.util.Pair;
import com.fr2501.util.SimpleFileWriter;
import com.fr2501.virage.types.Component;
import com.fr2501.virage.types.ComponentType;
import com.fr2501.virage.types.ComposableModule;
import com.fr2501.virage.types.CompositionalStructure;
import com.fr2501.virage.types.DecompositionTree;
import com.fr2501.virage.types.FrameworkRepresentation;

/**
 * Generator to create C code from compositions.
 *
 */
public final class CCodeGenerator {
    private final String codeFileTemplate;
    private final String compositionsTemplate;

    private final FrameworkRepresentation framework;

    public CCodeGenerator(final FrameworkRepresentation framework) {
        this.framework = framework;

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
                .getResourceAsStream("c_implementations/compositions.template");
        try {
            IOUtils.copy(compositionsTemplateStream, writer, StandardCharsets.UTF_8);
        } catch (final IOException e) {
            e.printStackTrace();
        }

        this.compositionsTemplate = writer.toString();
    }

    private Pair<Pair<String, String>, Integer> getCCodeFromComposition(
            final DecompositionTree composition, final int ctr) {
        String head = "";
        String body = "";

        final ComposableModule currentModule = this.framework
                .getComposableModule(composition.getLabel());
        if (currentModule != null) {
            head = composition.getLabel() + "(";

            for (int i = 0; i < composition.getChildren().size(); i++) {
                final DecompositionTree child = composition.getChildren().get(i);
                final String childLabel = child.getLabel();

                if ("_".equals(childLabel)) {
                    final ComponentType childType = this.framework
                            .getComponent(composition.getLabel()).getParameters().get(i);

                    if (childType.getName().equals("nat")) {
                        head += "1";
                    } else if (childType.getName().equals("rel")) {
                        head += "get_default_ordering(p)";
                    }
                } else {
                    head += this.getCCodeFromComposition(child, ctr).getFirstValue()
                            .getFirstValue();
                }

                head += ",";
            }

            head += "p,r)";
        }

        final CompositionalStructure currentStructure = this.framework
                .getCompositionalStructure(composition.getLabel());
        if (currentStructure != null) {
            final String structure = composition.getLabel();

            final Pattern pattern = Pattern.compile("// " + structure + ".*" + "// " + structure,
                    Pattern.DOTALL);
            final Matcher matcher = pattern.matcher(this.compositionsTemplate);

            if (matcher.find()) {
                String structureTemplate = matcher.group();

                structureTemplate = structureTemplate.replace("$IDX", String.valueOf(ctr));

                int moduleCounter = 1;
                for (final DecompositionTree child : composition.getChildren()) {
                    if (this.framework.getComposableModule(child.getLabel()) != null
                            || this.framework.getCompositionalStructure(child.getLabel()) != null) {
                        final Pair<Pair<String, String>, Integer> childCode = this
                                .getCCodeFromComposition(child, ctr + 1);

                        body += childCode.getFirstValue().getSecondValue() + System.lineSeparator();

                        structureTemplate = structureTemplate.replace(
                                "$MODULE_" + String.valueOf(moduleCounter),
                                childCode.getFirstValue().getFirstValue());
                        moduleCounter++;
                    } else if (this.framework.getComponent(child.getLabel()) != null) {
                        final Component currentComponent = this.framework
                                .getComponent(child.getLabel());
                        final ComponentType type = currentComponent.getType();

                        if (type.getName().equals("aggregator")) {
                            structureTemplate = structureTemplate.replace("$AGGREGATOR",
                                    currentComponent.getName());
                        } else if (type.getName().equals("termination_condition")) {
                            // TODO: This is completely non-generic and only admissible for the
                            // defer_eq_condition.
                            structureTemplate = structureTemplate.replace("$TERMINATION_CONDITION",
                                    currentComponent.getName() + "("
                                            + child.getChildren().get(0).getLabel() + ",p,r)");
                        }
                    }
                }

                body += structureTemplate;
                head = structure + "_" + String.valueOf(ctr) + "(p,r)";
            } else {
                throw new IllegalArgumentException();
            }
        }

        if (currentModule == null && currentStructure == null) {
            head = composition.getLabel();
        }

        return new Pair<Pair<String, String>, Integer>(new Pair<String, String>(head, body), ctr);
    }

    public File getCCodeFromComposition(final String compositionString) {
        final DecompositionTree composition = DecompositionTree.parseString(compositionString);
        final String cCode = "";

        final String entryName = "composition";

        final Pair<Pair<String, String>, Integer> res = this.getCCodeFromComposition(composition,
                0);

        String fileContents = this.codeFileTemplate.replace("$CONTENT",
                res.getFirstValue().getSecondValue());
        fileContents = fileContents.replace("$ENTRY", res.getFirstValue().getFirstValue());

        final File result = new File("target/generated-sources/voting_rule.c");
        (new SimpleFileWriter()).writeToFile(result.getAbsolutePath(), fileContents);

        return result;
    }

}
