package edu.kit.kastel.formal.virage.isabelle;

import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.io.StringWriter;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.apache.commons.io.IOUtils;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import edu.kit.kastel.formal.util.Pair;
import edu.kit.kastel.formal.util.SimpleFileWriter;
import edu.kit.kastel.formal.util.StringUtils;
import edu.kit.kastel.formal.util.SystemUtils;
import edu.kit.kastel.formal.virage.core.ConfigReader;
import edu.kit.kastel.formal.virage.prolog.ExtendedPrologStrings;
import edu.kit.kastel.formal.virage.prolog.PrologParser;
import edu.kit.kastel.formal.virage.prolog.PrologPredicate;
import edu.kit.kastel.formal.virage.prolog.SimplePrologParser;
import edu.kit.kastel.formal.virage.types.ComponentType;
import edu.kit.kastel.formal.virage.types.CompositionProof;
import edu.kit.kastel.formal.virage.types.FrameworkRepresentation;
import edu.kit.kastel.formal.virage.types.Parameterized;

/**
 * Generates a complete Isabelle theory file containing a module definition and (possibly) several
 * proofs.
 *
 * @author VeriVote
 */
public final class IsabelleTheoryGenerator {
    /**
     * Name separator between theories or modules.
     */
    public static final String NAME_SEPARATOR = "_";

    /**
     * Module name variable.
     */
    protected static final String VAR_MODULE_NAME = "$MODULE_NAME";

    /**
     * Module parameters variable.
     */
    protected static final String VAR_MODULE_PARAMETERS = "$MODULE_PARAMETERS";

    /**
     * The logger.
     */
    private static final Logger LOGGER = LogManager.getLogger(IsabelleTheoryGenerator.class);

    /**
     * File name for the theory template.
     */
    private static final String THEORY_TEMPLATE_FILE_NAME = "theory";

    /**
     * The name of generated theories.
     */
    private static final String THEORY_NAME = "generated_theory";

    /**
     * The name of generated modules.
     */
    private static final String MODULE_NAME = "Generated_module";

    /**
     * The theory name variable.
     */
    private static final String VAR_THEORY_NAME = "$THEORY_NAME";

    /**
     * The imports variable.
     */
    private static final String VAR_IMPORTS = "$IMPORTS";

    /**
     * The module parameter types variable.
     */
    private static final String VAR_MODULE_PARAM_TYPES = "$MODULE_PARAM_TYPES";

    /**
     * The module definition variable.
     */
    private static final String VAR_MODULE_DEF = "$MODULE_DEF";

    /**
     * The proofs variable.
     */
    private static final String VAR_PROOFS = "$PROOFS";

    /**
     * The template for generated theories.
     */
    private static String theoryTemplate = StringUtils.EMPTY;

    /**
     * Theory counter to generate unique names.
     */
    private static int theoryCounter;

    /**
     * Functions and definitions within the session.
     */
    private Map<String, String> functionsAndDefinitions;

    /**
     * The compositional framework.
     */
    private final FrameworkRepresentation framework;

    /**
     * The associated proof generator.
     */
    private final IsabelleProofGenerator generator;

    /**
     * The Prolog parser.
     */
    private final PrologParser parser;

    /**
     * Mapping from variables to their types.
     */
    private Map<String, String> typedVariables;

    /**
     * Simple constructor.
     * @param frameworkValue the compositional framework
     */
    public IsabelleTheoryGenerator(final FrameworkRepresentation frameworkValue) {
        this(frameworkValue.getTheoryPath(), frameworkValue);
    }

    /**
     * Simple constructor.
     *
     * @param theoryPath the path of the generated theory
     * @param frameworkValue the framework representation
     */
    public IsabelleTheoryGenerator(final String theoryPath,
                                   final FrameworkRepresentation frameworkValue) {
        if (IsabelleTheoryGenerator.theoryTemplate.isEmpty()) {
            final InputStream theoryTemplateStream = this.getClass().getClassLoader()
                    .getResourceAsStream(THEORY_TEMPLATE_FILE_NAME
                                        + IsabelleCodeGenerator.DOT_TMPL);
            final StringWriter writer = new StringWriter();
            try {
                IOUtils.copy(theoryTemplateStream, writer, StandardCharsets.UTF_8);
            } catch (final IOException e) {
                LOGGER.error(e);
            }
            setTheoryTemplate(writer.toString());
        }
        try {
            this.functionsAndDefinitions =
                    IsabelleTheoryParser.getAllFunctionsAndDefinitions(theoryPath);
        } catch (final IOException e) {
            LOGGER.error(e);
        }
        this.framework = frameworkValue;
        this.generator = new IsabelleProofGenerator(this, this.functionsAndDefinitions);
        this.parser = new SimplePrologParser();
        this.typedVariables = new HashMap<String, String>();
    }

    private static synchronized void setTheoryTemplate(final String newTemplate) {
        theoryTemplate = newTemplate;
    }

    private static synchronized void incrementTheoryCounter() {
        theoryCounter++;
    }

    private static String findImportsFromCompositionRules(final List<CompositionProof> proofs,
                                                          final String sessionName) {
        final Set<String> origins = new HashSet<String>();
        for (final CompositionProof proof: proofs) {
            origins.addAll(proof.getAllOrigins());
        }
        boolean usingUnprovenFacts = false;
        final Set<String> originStrings = new HashSet<String>();
        for (final String origin: origins) {
            if (origin.contains(IsabelleUtils.DOT_THY)) {
                // Isabelle expects imports without suffix.
                originStrings.add(origin.replace(IsabelleUtils.DOT_THY, StringUtils.EMPTY));
            } else {
                if (ExtendedPrologStrings.UNPROVEN.equals(origin)) {
                    // Proof relies on unproven facts, add a comment explaining this.
                    usingUnprovenFacts = true;
                }
            }
        }
        final StringBuilder r = new StringBuilder();
        for (final String origin: originStrings) {
            r.append(StringUtils.addSpace(sessionName
                     + IsabelleUtils.THEORY_NAME_SEPARATOR + origin));
        }
        String res = r.toString();
        if (usingUnprovenFacts) {
            res += System.lineSeparator() + System.lineSeparator()
                    + StringUtils.isabelleCommentBlock(
                            "Some proofs appear to rely on facts not yet",
                            " proven within Isabelle/HOL. Check Isabelle",
                            "    error messages for more information.   ");
        }
        return res;
    }

    private static String buildOutputPath(final String previousPath, final String theoryName) {
        String outputPath = previousPath;
        if (!outputPath.endsWith(IsabelleUtils.DOT_THY)) {
            if (!outputPath.endsWith(File.separator)) {
                outputPath = outputPath + File.separator;
            }
            outputPath = outputPath + theoryName + IsabelleUtils.DOT_THY;
        }
        return outputPath;
    }

    private static String generateModuleParameterTypes(final List<String> moduleParametersList,
                                                       final Map<String, String> typedVariables) {
        final List<String> moduleParamTypesList = new LinkedList<String>();
        for (int i = 0; i < moduleParametersList.size(); i++) {
            for (final Map.Entry<String, String> module: typedVariables.entrySet()) {
                if (module.getValue().equals(moduleParametersList.get(i))) {
                    final StringBuilder moduleParamType =
                            IsabelleUtils.isSimpleType(module.getKey())
                            ? new StringBuilder()
                                    // Simple types (e.g., natural numbers) do not require "'a".
                                    : new StringBuilder(
                                            StringUtils.addSpace(IsabelleUtils.TYPE_ALIAS));
                    moduleParamType.append(
                            StringUtils.addSpace(StringUtils.printCollection2(
                                    module.getKey(), IsabelleUtils.RIGHT_ARROW)));
                    moduleParamTypesList.add(i, moduleParamType.toString());
                }
            }
        }
        final StringBuilder moduleParamTypes = new StringBuilder();
        for (final String type: moduleParamTypesList) {
            moduleParamTypes.append(type);
        }
        return moduleParamTypes.toString();
    }

    private static Pair<String, String> buildModuleDef(final Map<String, Set<String>> moduleDefMap,
                                                       final String importsParam,
                                                       final String sessionName) {
        final Set<String> imports = new LinkedHashSet<String>();
        imports.add(importsParam);
        // There exists only one element, otherwise there is an exception thrown beforehand.
        final String moduleDef = new ArrayList<String>(moduleDefMap.keySet()).get(0);
        // imports.add(sessionName + StringUtils.PERIOD + moduleDef);
        // Additional imports might have occurred, which are only relevant
        // for the definition of the module, but not used within the proofs.
        // Add those.
        for (final String importString: new ArrayList<Set<String>>(moduleDefMap.values()).get(0)) {
            final String importStringWithoutSuffix =
                    importString.replace(IsabelleUtils.DOT_THY, StringUtils.EMPTY);
            if (!imports.contains(importStringWithoutSuffix)) {
                final String importWithSuffix =
                        sessionName + StringUtils.PERIOD + importStringWithoutSuffix;
                imports.add(importWithSuffix);
            }
        }
        // Build string from chain of imports
        final StringBuilder importBuild = new StringBuilder(importsParam);
        for (final String entry: imports) {
            importBuild.append(StringUtils.surroundWithSpaces(entry));
        }
        final String importString =
                importBuild.toString().isBlank() ? IsabelleUtils.MAIN : importBuild.toString();
        return new Pair<String, String>(moduleDef, importString);
    }

    private static String replaceVariables(final String theoryName, final String imports,
                                           final String moduleParamTypes, final String moduleName,
                                           final String moduleParameters, final String moduleDef,
                                           final String proofs) {
        return IsabelleTheoryGenerator.theoryTemplate
                .replace(VAR_PROOFS, proofs)
                .replace(VAR_THEORY_NAME, theoryName)
                .replace(VAR_IMPORTS, imports)
                .replace(VAR_MODULE_PARAM_TYPES, moduleParamTypes)
                .replace(VAR_MODULE_DEF, moduleDef)
                .replace(VAR_MODULE_NAME, moduleName)
                .replace(VAR_MODULE_PARAMETERS, moduleParameters);
    }

    /**
     * This method takes a set of {@link CompositionProof} objects and a composition, translates
     * this information to Isabelle syntax and writes its result to a file.
     *
     * @param passedComposition the composition
     * @param proofs proofs for all the claimed properties
     * @param passedOutputPath a path to the folder to which the result shall be written. If path
     *     points to a file, this file will be overwritten and the name will most probably not
     *     correspond to the theory inside, so Isabelle will not be able to verify it.
     * @return the {@link File} containing the results
     * @throws IllegalArgumentException if any of the arguments is malformed
     */
    public File generateTheoryFile(final String passedComposition,
                                   final List<CompositionProof> proofs,
                                   final String passedOutputPath) {
        this.typedVariables = new HashMap<String, String>();
        final String theoryName =
                THEORY_NAME + NAME_SEPARATOR + IsabelleTheoryGenerator.theoryCounter;
        final String moduleName =
                MODULE_NAME + NAME_SEPARATOR + IsabelleTheoryGenerator.theoryCounter;
        incrementTheoryCounter();
        final PrologPredicate proofPredicate =
                parser.parsePredicate(StringUtils.removeWhitespace(passedComposition));
        this.replacePrologVariables(proofPredicate);
        // This looks tedious, but is required to ensure correct ordering of variables in
        // definition. This assumes that variable names are given in the correct order,
        // ascending alphabetically. This might seem arbitrary, but is ensured
        // by the way IsabelleUtils.findUnusedVariables works.
        final List<String> moduleParametersList = new LinkedList<String>();
        for (final Map.Entry<String, String> module: this.typedVariables.entrySet()) {
            moduleParametersList.add(module.getValue());
        }
        Collections.sort(moduleParametersList);
        final StringBuilder moduleParameters = new StringBuilder();
        for (final String param: moduleParametersList) {
            moduleParameters.append(StringUtils.prefixSpace(param));
        }
        final String moduleParameterString = moduleParameters.toString();
        final String moduleParameterTypeString =
                generateModuleParameterTypes(moduleParametersList, this.typedVariables);
        final String imports =
                findImportsFromCompositionRules(proofs, this.framework.getSessionName());
        final Map<String, Set<String>> moduleDefMap =
                IsabelleUtils.translatePrologToIsabelle(this.functionsAndDefinitions,
                                                        proofPredicate);
        if (moduleDefMap.size() != 1) {
            throw new IllegalArgumentException();
        }
        final Pair<String, String> moduleDefResult =
                buildModuleDef(moduleDefMap, imports, this.framework.getSessionName());
        if (moduleDefResult.getSecondValue().isBlank()) {
            throw new IllegalArgumentException();
        }
        final StringBuilder proofsString = new StringBuilder();
        for (final CompositionProof proof: proofs) {
            proofsString.append(this.generator.generateIsabelleProof(proof)
                                + System.lineSeparator() + System.lineSeparator());
        }
        final String fileContents =
                replaceVariables(theoryName, moduleDefResult.getSecondValue(),
                                 moduleParameterTypeString, moduleName, moduleParameterString,
                                 moduleDefResult.getFirstValue(), proofsString.toString());
        final SimpleFileWriter writer = new SimpleFileWriter();
        final String outputPath = buildOutputPath(passedOutputPath, theoryName);
        writer.writeToFile(outputPath, fileContents);
        return SystemUtils.file(outputPath);
    }

    /**
     * Generate an Isabelle theory file.
     *
     * @param composition the composition
     * @param proofs the proofs
     * @return the theory file
     */
    public File generateTheoryFile(final String composition, final List<CompositionProof> proofs) {
        return this.generateTheoryFile(composition, proofs,
                                       ConfigReader.getInstance().getDefaultOutputPath());
    }

    /**
     * Return a representation of the framework.
     *
     * @return the framework representation
     */
    protected FrameworkRepresentation getFramework() {
        return this.framework;
    }

    /**
     * Returns a map of the typed variables.
     *
     * @return the typed variables' map
     */
    protected Map<String, String> getTypedVariables() {
        return this.typedVariables;
    }

    /**
     * Replaces variable symbols used by Prolog with those used by Isabelle.
     *
     * @param predicate the Prolog predicate
     * @throws IllegalArgumentException if the predicate component is unknown
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
}
