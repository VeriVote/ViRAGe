package com.fr2501.virage.isabelle;

import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.io.StringWriter;
import java.nio.charset.StandardCharsets;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.apache.commons.io.IOUtils;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import com.fr2501.util.SimpleFileWriter;
import com.fr2501.util.StringUtils;
import com.fr2501.virage.prolog.ExtendedPrologStrings;
import com.fr2501.virage.prolog.PrologParser;
import com.fr2501.virage.prolog.PrologPredicate;
import com.fr2501.virage.prolog.SimplePrologParser;
import com.fr2501.virage.types.ComponentType;
import com.fr2501.virage.types.CompositionProof;
import com.fr2501.virage.types.FrameworkRepresentation;
import com.fr2501.virage.types.Parameterized;

/**
 * Generates a complete Isabelle theory file containing a module definition and (possibly) several
 * proofs.
 *
 */
public final class IsabelleTheoryGenerator {
    protected static final String VAR_MODULE_NAME = "$MODULE_NAME";
    protected static final String VAR_MODULE_PARAMETERS = "$MODULE_PARAMETERS";

    private static final Logger LOGGER = LogManager.getLogger(IsabelleTheoryGenerator.class);

    private static final String VAR_THEORY_NAME = "$THEORY_NAME";
    private static final String VAR_IMPORTS = "$IMPORTS";
    private static final String VAR_MODULE_PARAM_TYPES = "$MODULE_PARAM_TYPES";
    private static final String VAR_MODULE_DEF = "$MODULE_DEF";
    private static final String VAR_PROOFS = "$PROOFS";

    private static final String THEORY_NAME = "generated_theory";
    private static final String MODULE_NAME = "Generated_module";
    private static final String RIGHT_ARROW = " => ";
    private static final String TYPE = "'a ";

    // TODO config
    private static final String DEFAULT_PATH = "../virage/target/generated-sources";

    private static String theoryTemplate = "";
    private static int theoryCounter;
    private Map<String, String> functionsAndDefinitions;
    private final FrameworkRepresentation framework;

    private final IsabelleProofGenerator generator;
    private final PrologParser parser;

    private Map<String, String> typedVariables;

    public IsabelleTheoryGenerator(final FrameworkRepresentation framework) {
        this(framework.getTheoryPath(), framework);
    }

    /**
     * Simple constructor.
     *
     * @param theoryPath the path of the generated theory
     * @param framework the framework representation
     */
    public IsabelleTheoryGenerator(final String theoryPath,
            final FrameworkRepresentation framework) {
        if (theoryTemplate.isEmpty()) {
            final InputStream theoryTemplateStream = this.getClass().getClassLoader()
                    .getResourceAsStream("theory.template");
            final StringWriter writer = new StringWriter();
            try {
                IOUtils.copy(theoryTemplateStream, writer, StandardCharsets.UTF_8);
            } catch (final IOException e) {
                LOGGER.error("Something went wrong.", e);
            }
            theoryTemplate = writer.toString();
        }

        final IsabelleTheoryParser parser = new IsabelleTheoryParser();

        try {
            this.functionsAndDefinitions = parser.getAllFunctionsAndDefinitions(theoryPath);
        } catch (final IOException e) {
            LOGGER.error("Something went wrong.", e);
        }

        this.framework = framework;
        this.generator = new IsabelleProofGenerator(this, this.functionsAndDefinitions);
        this.parser = new SimplePrologParser();
        this.typedVariables = new HashMap<String, String>();
    }

    private String findImportsFromCompositionRules(final List<CompositionProof> proofs) {
        String res = "";

        final Set<String> origins = new HashSet<String>();
        for (final CompositionProof proof : proofs) {
            origins.addAll(proof.getAllOrigins());
        }

        boolean usingUnprovenFacts = false;
        final Set<String> originStrings = new HashSet<String>();
        for (final String origin : origins) {
            if (origin.contains(IsabelleUtils.FILE_EXTENSION)) {
                // Isabelle expects imports without suffix.
                originStrings.add(origin.replace(IsabelleUtils.FILE_EXTENSION, ""));
            } else {
                if (origin.equals(ExtendedPrologStrings.UNPROVEN)) {
                    // Proof relies on unproven facts, add a comment explaining this.
                    usingUnprovenFacts = true;
                }
            }
        }

        for (final String origin : originStrings) {
            res += this.framework.getSessionName() + "." + origin + " ";
        }

        if (usingUnprovenFacts) {
            res += "\n\n" + "(* * * * * * * * * * * * * * * * * * * * * * * *)\n"
                    + "(* Some proofs appear to rely on facts not yet *)\n"
                    + "(*  proven within Isabelle/HOL. Check Isabelle *)\n"
                    + "(*     error messages for more information.    *)\n"
                    + "(* * * * * * * * * * * * * * * * * * * * * * * *)";
        }

        return res;
    }

    public File generateTheoryFile(final String composition, final List<CompositionProof> proofs) {
        return this.generateTheoryFile(composition, proofs, DEFAULT_PATH);
    }

    /**
     * This method takes a Set of {@link CompositionProof} objects and a composition, translates
     * this information to Isabelle syntax and writes its result to a file.
     *
     * @param composition the composition
     * @param proofs proofs for all the claimed properties
     * @param outputPath a path to the folder to which the result shall be written. If path points
     *      to a file, this file will be overwritten and the name will most probably not correspond to
     *      the theory inside, so Isabelle won't be able to verify it.
     * @return the {@link File} containing the results
     */
    public File generateTheoryFile(final String passedComposition, final List<CompositionProof> proofs,
            final String passedOutputPath) {
        final String composition = StringUtils.removeWhitespace(passedComposition);

        this.typedVariables = new HashMap<String, String>();

        final String theoryName = THEORY_NAME + "_" + theoryCounter;
        final String moduleName = MODULE_NAME + "_" + theoryCounter;
        theoryCounter++;

        final PrologPredicate proofPredicate = this.parser.parsePredicate(composition);
        this.replacePrologVariables(proofPredicate);
        String moduleParameters = "";

        // This looks tedious, but is required to ensure correct
        // ordering of variables in definition.
        // This assumes that variable names are given in the correct order,
        // ascending alphabetically. This might seem arbitrary, but is ensured
        // by the way IsabelleUtils.findUnusedVariables works.
        final List<String> moduleParametersList = new LinkedList<String>();
        for (final String type : this.typedVariables.keySet()) {
            moduleParametersList.add(this.typedVariables.get(type));
        }

        Collections.sort(moduleParametersList);
        for (final String param : moduleParametersList) {
            moduleParameters += " " + param;
        }

        final List<String> moduleParamTypesList = new LinkedList<String>();
        for (int i = 0; i < moduleParametersList.size(); i++) {
            for (final String type : this.typedVariables.keySet()) {
                if (this.typedVariables.get(type).equals(moduleParametersList.get(i))) {
                    String moduleParamType = "";
                    // Simple types like nat don't require an "'a".
                    if (!IsabelleUtils.isSimpleType(type)) {
                        moduleParamType = TYPE;
                    }

                    moduleParamType += type + RIGHT_ARROW;
                    moduleParamTypesList.add(i, moduleParamType);
                }
            }
        }

        String moduleParamTypes = "";
        for (final String type : moduleParamTypesList) {
            moduleParamTypes += type;
        }
        // -----

        String imports = this.findImportsFromCompositionRules(proofs);

        final Map<String, Set<String>> moduleDefMap = IsabelleUtils
                .translatePrologToIsabelle(this.functionsAndDefinitions, proofPredicate);
        if (moduleDefMap.keySet().size() != 1) {
            throw new IllegalArgumentException();
        }

        // There will be only one iteration, but it is a bit tedious to extract
        // single elements from sets.
        String moduleDef = "";
        for (final String string : moduleDefMap.keySet()) {
            moduleDef = string;

            // Additional imports might have occured, which are only relevant
            // for the definition of the module, but not used within the proofs.
            // Add those.
            for (final String importString : moduleDefMap.get(string)) {
                final String importStringWithoutSuffix = importString
                        .replace(IsabelleUtils.FILE_EXTENSION, "");

                if (!imports.contains(importStringWithoutSuffix)) {
                    imports += " " + this.framework.getSessionName() + "."
                            + importStringWithoutSuffix + " ";
                }
            }
        }

        String proofsString = "";
        for (final CompositionProof proof : proofs) {
            proofsString += this.generator.generateIsabelleProof(proof) + "\n\n";
        }

        final String fileContents = this.replaceVariables(theoryName, imports, moduleParamTypes,
                moduleName, moduleParameters, moduleDef, proofsString);

        final SimpleFileWriter writer = new SimpleFileWriter();

        String outputPath = passedOutputPath;

        if (!outputPath.endsWith(IsabelleUtils.FILE_EXTENSION)) {
            if (!outputPath.endsWith(File.separator)) {
                outputPath = outputPath + File.separator;
            }
            outputPath = outputPath + theoryName + IsabelleUtils.FILE_EXTENSION;
        }

        try {
            writer.writeToFile(outputPath, fileContents);

            return new File(outputPath).getCanonicalFile();
        } catch (final IOException e) {
            LOGGER.error("Something went wrong.", e);
        }

        return null;
    }

    protected FrameworkRepresentation getFramework() {
        return this.framework;
    }

    protected Map<String, String> getTypedVariables() {
        return this.typedVariables;
    }

    /**
     * Replaces variable symbols used by Prolog with those used by Isabelle.
     *
     * @param predicate the Prolog predicate
     */
    protected void replacePrologVariables(final PrologPredicate predicate) {
        for (int i = 0; i < predicate.getParameters().size(); i++) {
            final PrologPredicate child = predicate.getParameters().get(i);

            if (child.isVariable()) {
                Parameterized component = this.framework.getComponent(predicate.getName());

                if (component == null) {
                    component = this.framework.getCompositionalStructure(predicate.getName());
                }

                if (component == null) {
                    throw new IllegalArgumentException("Unknown component: " + predicate.getName());
                }

                final ComponentType childType = component.getParameters().get(i);

                if (!this.typedVariables.containsKey(childType.getName())) {
                    this.typedVariables.put(childType.getName(),
                            IsabelleUtils.getUnusedVariable(predicate.toString()));
                }

                child.setName(this.typedVariables.get(childType.getName()));
            }

            this.replacePrologVariables(child);
        }
    }

    private String replaceVariables(final String theoryName, final String imports,
            final String moduleParamTypes, final String moduleName, final String moduleParameters,
            final String moduleDef, final String proofs) {
        String res = theoryTemplate;

        res = res.replace(VAR_PROOFS, proofs);

        res = res.replace(VAR_THEORY_NAME, theoryName);
        res = res.replace(VAR_IMPORTS, imports);
        res = res.replace(VAR_MODULE_PARAM_TYPES, moduleParamTypes);
        res = res.replace(VAR_MODULE_DEF, moduleDef);

        res = res.replace(VAR_MODULE_NAME, moduleName);
        res = res.replace(VAR_MODULE_PARAMETERS, moduleParameters);

        return res;
    }
}
