package edu.kit.kastel.formal.virage.types;

import java.io.File;
import java.time.ZonedDateTime;
import java.time.format.DateTimeFormatter;
import java.util.Collections;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import edu.kit.kastel.formal.util.Pair;
import edu.kit.kastel.formal.util.SimpleFileWriter;
import edu.kit.kastel.formal.util.StringUtils;
import edu.kit.kastel.formal.virage.core.ConfigReader;
import edu.kit.kastel.formal.virage.core.VirageCore;
import edu.kit.kastel.formal.virage.isabelle.IsabelleUtils;
import edu.kit.kastel.formal.virage.prolog.ExtendedPrologStrings;
import edu.kit.kastel.formal.virage.prolog.PrologClause;
import edu.kit.kastel.formal.virage.prolog.PrologParser;
import edu.kit.kastel.formal.virage.prolog.PrologPredicate;
import edu.kit.kastel.formal.virage.prolog.SimplePrologParser;

/**
 * The data model required to represent the compositional framework as a whole. It is designed for
 * the electoral module framework, but not at all limited to it.
 *
 * @author VeriVote
 */
public final class FrameworkRepresentation {
    /**
     * The logger.
     */
    private static final Logger LOGGER = LogManager.getLogger(FrameworkRepresentation.class);

    /**
     * Separator for generated (E)PL files.
     */
    private static final String SEPARATOR = "%%%%%%%%%%%%%%%%%%%%" + System.lineSeparator();

    /**
     * Path to the (E)PL file.
     */
    private String absolutePath;

    /**
     * Path to Isabelle theories.
     */
    private String theoryPath;

    /**
     * Name of the Isabelle session.
     */
    private String sessionName;

    /**
     * Set of component types.
     */
    private final Set<ComponentType> componentTypes;

    /**
     * Set of components.
     */
    private final Set<Component> components;

    /**
     * Set of modules that can be composed.
     */
    private final Set<ComposableModule> composableModules;

    /**
     * Set of compositional structures.
     */
    private final Set<CompositionalStructure> compositionalStructures;

    /**
     * Set of composition rules.
     */
    private final List<CompositionRule> compositionRules;

    /**
     * Set of properties.
     */
    private final Set<Property> properties;

    /**
     * List of type synonyms.
     */
    private List<Pair<String, String>> typeSynonyms;

    /**
     * List of atomic types.
     */
    private List<ComponentType> atomicTypes;

    /**
     * Alias for modules that can be composed.
     * <b>Warning:</b> This was set to deprecated with no explicit justification,
     * maybe handle with care.
     */
    private String composableModuleAlias;

    /*
     * public FrameworkRepresentation() { this(null); }
     */

    /**
     * Simple constructor.
     *
     * @param absolutePathValue path to the EPL file
     */
    public FrameworkRepresentation(final String absolutePathValue) {
        this.absolutePath = absolutePathValue;
        this.componentTypes = new HashSet<ComponentType>();
        this.components = new HashSet<Component>();
        this.composableModules = new HashSet<ComposableModule>();
        this.compositionalStructures = new HashSet<CompositionalStructure>();
        this.compositionRules = new LinkedList<CompositionRule>();
        this.properties = new HashSet<Property>();
    }

    private static PrologPredicate addPredicateAliases(final PrologParser parser,
                                                       final Property p, final int arity,
                                                       final String prefix, final String alias) {
        final List<PrologPredicate> newParams = new LinkedList<PrologPredicate>();
        for (int j = 0; j < p.getArity(); j++) {
            if (arity == j) {
                newParams.add(parser.parsePredicate(alias));
            } else {
                newParams.add(new PrologPredicate(prefix + j));
            }
        }
        return new PrologPredicate(p.getName(), newParams);
    }

    /**
     * Adds a @link{Component} to the FrameworkRepresentation. Performs type check without throwing
     * any exceptions.
     *
     * @param c the @link{Component} to be added
     */
    public void add(final Component c) {
        this.checkTypes(c);
        this.components.add(c);
    }

    /**
     * Adds a @link{ComponentType} to the FrameworkRepresentation.
     *
     * @param ct the @link{ComponentType} to be added
     */
    public void add(final ComponentType ct) {
        this.componentTypes.add(ct);
    }

    /**
     * Adds a @link{ComposableModule} to the FrameworkRepresentation Performs type check without
     * throwing any exceptions.
     *
     * @param cm the @link{ComposableModule} to be added
     */
    public void add(final ComposableModule cm) {
        this.checkTypes(cm);
        this.composableModules.add(cm);
    }

    /**
     * Adds a @link{CompositionalStructure} to the FrameworkRepresentation Performs type check
     * without throwing any exceptions.
     * <b>Warning:</b> This was set to deprecated with no explicit justification,
     * maybe handle with care.
     *
     * @param structure the @link{CompositionalStructure} to be added
     */
    public void add(final CompositionalStructure structure) {
        // this.checkTypes(structure);
        this.compositionalStructures.add(structure);
    }

    /**
     * Adds a @link{CompositionRule} to the FrameworkRepresentation.
     *
     * @param rule the @link{ComposiotionRule} to be added
     */
    public void add(final CompositionRule rule) {
        /*
         * PrologClause actualClause = this.removeAtomicTypesFromClause(cr.getClause());
         * if (actualClause == null) { return; }
         *
         * rule = new CompositionRule(cr.getName(), cr.getOrigin(), actualClause);
         */
        for (final CompositionRule cr: this.compositionRules) {
            if (cr.equals(rule)) {
                return;
            }
        }
        this.compositionRules.add(rule);
    }

    /**
     * Adds a {@link Property} to the FrameworkRepresentation Performs type check without throwing
     * any exceptions.
     *
     * @param p the {@link Property} to be added
     */
    public void add(final Property p) {
        this.checkTypes(p);
        this.properties.add(p);
    }

    /**
     * Adds dummy rules (e.g. ($property)_intro) and alias rules if these are required.
     */
    public void addDummyAndAliasRulesIfNecessary() {
        this.addDummyRules();
        this.addAliasRules();
    }

    private void addAliasRules() {
        final Map<String, String> aliases = ConfigReader.getInstance().getComponentAliases();
        final PrologParser parser = new SimplePrologParser();
        for (final Property p: this.properties) {
            for (int i = 0; i < p.getArity(); i++) {
                final ComponentType propertyType = p.getParameters().get(i);
                int aliasIdx = 0;
                for (final Map.Entry<String, String> aliasEntry: aliases.entrySet()) {
                    final PrologPredicate aliasPredicate =
                            parser.parsePredicate(aliasEntry.getKey());
                    final String aliasName = aliasPredicate.getName();
                    final Component aliasComponent = this.getComponent(aliasName);
                    if (aliasComponent != null && !aliasComponent.getType().equals(propertyType)) {
                        continue;
                    }
                    final String nextFreeVariable = "ALIAS_VAR_";
                    final PrologPredicate newSucc =
                        addPredicateAliases(parser, p, i, nextFreeVariable, aliasEntry.getKey());
                    final PrologPredicate newAnte =
                        addPredicateAliases(parser, p, i, nextFreeVariable, aliasEntry.getValue());
                    final PrologClause clause = new PrologClause(newSucc, newAnte);
                    final CompositionRule rule =
                            new CompositionRule(p.getName() + "_alias_" + aliasIdx,
                                                ExtendedPrologStrings.ASSUMPTION,
                                                clause);
                    this.add(rule);
                    /*
                     * final PrologClause clause2 = new PrologClause(newAnte, newSucc); final
                     * CompositionRule rule2 = new CompositionRule(p.getName() + "_alias_inv_" +
                     * aliasIdx, ExtendedPrologStrings.ASSUMPTION, clause2); this.add(rule2);
                     */
                    this.updateFile();
                    aliasIdx++;
                }
            }
        }
    }

    /**
     * Adds dummy rules (e.g. ($property)_intro).
     */
    private void addDummyRules() {
        final List<String> atomicTypeStrings = ConfigReader.getInstance().getAtomicTypes();
        this.atomicTypes = new LinkedList<ComponentType>();
        for (final String s: atomicTypeStrings) {
            final ComponentType type = new ComponentType(s);
            this.add(type);
            this.atomicTypes.add(type);
        }

        for (final Property p: this.properties) {
            boolean allAtomicTypes = true;
            for (final ComponentType type: p.getParameters()) {
                if (!this.atomicTypes.contains(type)) {
                    allAtomicTypes = false;
                    break;
                }
            }

            if (allAtomicTypes) {
                // A new rule is added such that the atomic properties are ignored.
                final List<PrologPredicate> params = new LinkedList<PrologPredicate>();
                for (int i = 0; i < p.getParameters().size(); i++) {
                    params.add(new PrologPredicate(PrologPredicate.ANONYMOUS));
                }
                p.setAtomic(true);
                final PrologPredicate pred = new PrologPredicate(p.getName(), params);
                final PrologClause clause = new PrologClause(pred);
                final CompositionRule rule =
                        new CompositionRule(p.getName() + "_intro",
                                            ExtendedPrologStrings.ASSUMPTION, clause);
                this.add(rule);
                this.updateFile();
            }
        }
    }

    private void checkTypes(final Parameterized object) {
        for (final ComponentType paramType: object.getParameters()) {
            if (!this.componentTypes.contains(paramType)) {
                LOGGER.info("Added item with unknown parameter type \"" + paramType.getName()
                        + StringUtils.PERIOD);
            }
        }
    }

    private void checkTypes(final Typed object) {
        final ComponentType type = object.getType();
        if (!this.componentTypes.contains(type)) {
            LOGGER.info("Added item with unknown type \"" + type.getName() + StringUtils.PERIOD);
        }
    }

    private void checkTypes(final TypedAndParameterized object) {
        this.checkTypes((Typed) object);
        this.checkTypes((Parameterized) object);
    }

    private String createHeader() {
        String res = SEPARATOR;
        final DateTimeFormatter dtf = DateTimeFormatter.ofPattern("yyyy-MM-dd HH:mm:ss z");
        final ZonedDateTime now = ZonedDateTime.now();
        res += StringUtils.sentence(
                "%% Generated by ViRAGe " + VirageCore.getVersion() + " at " + dtf.format(now));
        res += SEPARATOR;
        res += StringUtils.sentence(
                "%% To add new composition rules, go to the bottom of this file")
                + "%% A rule definition consists of three parts. "
                + "The first one represents its origin," + System.lineSeparator()
                + "%% for user defined rules this will always be \"UNPROVEN\". The second part is"
                + System.lineSeparator()
                + StringUtils.sentence(
                        "%% the symbolic name of the rule that will be used in generated proofs")
                + StringUtils.sentence(
                        "%% The third part is a Prolog clause capturing the semantics of the rule")
                + "%%" +  System.lineSeparator() + "%% Example:" + System.lineSeparator()
                + "%% % = UNPROVEN" + System.lineSeparator()
                + StringUtils.sentence(
                        "%% % example_rule_without_meaning" + System.lineSeparator()
                                + "%% property_a(X) :- property_b(X)");
        res += SEPARATOR;
        return res;
    }

    /**
     * Get the absolute path as a string.
     *
     * @return the absolute path
     */
    public String getAbsolutePath() {
        return this.absolutePath;
    }

    /**
     * Get the module's alias string.
     *
     * @return the module's alias
     */
    public String getAlias() {
        return this.composableModuleAlias;
    }

    /**
     * Returns the {@link Component} with the given name.
     *
     * @param name the name
     * @return the {@link Component}, null if it does not exist.
     */
    public Component getComponent(final String name) {
        for (final Component component: this.components) {
            if (component.getName().equals(name)) {
                return component;
            }
        }
        for (final ComposableModule module: this.composableModules) {
            if (module.getName().equals(name)) {
                return module;
            }
        }
        return null;
    }

    /**
     * Get components.
     *
     * @return the components
     */
    public Set<Component> getComponents() {
        return this.components;
    }

    /**
     * Get component types.
     *
     * @return the component types
     */
    public Set<ComponentType> getComponentTypes() {
        return this.componentTypes;
    }

    /**
     * Returns the {@link ComposableModule} with the given name.
     *
     * @param name the name
     * @return the {@link ComposableModule}, null if it does not exist.
     */
    public ComposableModule getComposableModule(final String name) {
        for (final ComposableModule module: this.composableModules) {
            if (module.getName().equals(name)) {
                return module;
            }
        }
        return null;
    }

    /**
     * Get the modules that can be composed.
     *
     * @return the modules that can be composed
     */
    public Set<ComposableModule> getComposableModules() {
        return this.composableModules;
    }

    /**
     * Returns the {@link CompositionalStructure} with the given name.
     *
     * @param name the name
     * @return the {@link CompositionalStructure}, null if it does not exist.
     */
    public CompositionalStructure getCompositionalStructure(final String name) {
        for (final CompositionalStructure component: this.compositionalStructures) {
            if (component.getName().equals(name)) {
                return component;
            }
        }
        return null;
    }

    /**
     * Get the compositional structures.
     *
     * @return the compositional structures
     */
    public Set<CompositionalStructure> getCompositionalStructures() {
        return this.compositionalStructures;
    }

    /**
     * Get the composition rules.
     *
     * @return the composition rules
     */
    public List<CompositionRule> getCompositionRules() {
        return this.compositionRules;
    }

    /**
     * Get the properties as a set.
     *
     * @return the properties
     */
    public Set<Property> getProperties() {
        return this.properties;
    }

    /**
     * Returns the {@link Property} with the given name.
     *
     * @param name the name
     * @return the {@link Property}, null if it does not exist.
     */
    public Property getProperty(final String name) {
        for (final Property property: this.properties) {
            if (property.getName().equals(name)) {
                return property;
            }
        }
        return null;
    }

    /**
     * Get the session's name.
     *
     * @return the session name string
     */
    public String getSessionName() {
        return this.sessionName;
    }

    /**
     * Get the theory path.
     *
     * @return the theory path string
     */
    public String getTheoryPath() {
        return this.theoryPath;
    }

    /**
     * Get the current type synonyms.
     *
     * @return the type synonyms as a list
     */
    public List<Pair<String, String>> getTypeSynonyms() {
        return this.typeSynonyms;
    }

    /**
     * Set new absolute path.
     *
     * @param newAbsolutePath the new absolute path string
     */
    public void setAbsolutePath(final String newAbsolutePath) {
        this.absolutePath = newAbsolutePath;
    }

    /**
     * Set new module alias.
     *
     * @param alias the new alias string
     */
    public void setAlias(final String alias) {
        this.composableModuleAlias = alias;
    }

    /**
     * Set new session name.
     *
     * @param newSessionName the new session name
     */
    public void setSessionName(final String newSessionName) {
        this.sessionName = newSessionName;
    }

    /**
     * Simple setter.
     *
     * @param newTheoryPath the theory path.
     */
    public void setTheoryPath(final String newTheoryPath) {
        String theoryPathCopy = newTheoryPath;
        if (!newTheoryPath.endsWith(File.separator)) {
            theoryPathCopy = newTheoryPath + File.separator;
        }
        this.theoryPath = theoryPathCopy;
    }

    /**
     * Set new type synonyms.
     *
     * @param newTypeSynonyms new type synonyms
     */
    public void setTypeSynonyms(final List<Pair<String, String>> newTypeSynonyms) {
        this.typeSynonyms = newTypeSynonyms;
    }

    /**
     * Creates a string representation of this in the EPL format.
     *
     * @return the string representation
     */
    public String toEplString() {
        Collections.sort(this.compositionRules);
        String res = this.createHeader();
        res += StringUtils.addSpace("% ====") + this.theoryPath + IsabelleUtils.ROOT
                + " - " + this.sessionName + System.lineSeparator();
        res += ExtendedPrologStrings.COMMENT + System.lineSeparator();
        res += StringUtils.addSpace(ExtendedPrologStrings.COMMENT)
                + ExtendedPrologStrings.COMPOSITION_TYPE_HEADER + System.lineSeparator();
        for (final ComponentType type: this.componentTypes) {
            res += StringUtils.addSpace("% ==") + type.getName() + System.lineSeparator();
            for (final Component comp: this.components) {
                if (comp.getType().equals(type)) {
                    res += StringUtils.addSpace(ExtendedPrologStrings.COMMENT)
                            + comp.toStringWithoutTypeSignature() + System.lineSeparator();
                }
            }
        }
        res += ExtendedPrologStrings.COMMENT + System.lineSeparator();

        /*
         * res += "% === composable_module" +  + System.lineSeparator(); res +=
         * StringUtils.sentence("%% This area is deprecated and therefore intentionally empty");
         *
         * res += "% === compositional_structure" +  + System.lineSeparator(); res +=
         * StringUtils.sentence("%% This area is deprecated and therefore intentionally empty");
         *
         * res += "%" +  + System.lineSeparator();
         */

        res += StringUtils.addSpace(ExtendedPrologStrings.COMMENT)
                + ExtendedPrologStrings.PROPERTY_HEADER + System.lineSeparator();
        for (final Property prop: this.properties) {
            res += StringUtils.addSpace(ExtendedPrologStrings.COMMENT) + prop.toString()
                    + System.lineSeparator();
        }
        final List<String> additionalProperties = ConfigReader.getInstance()
                .getAdditionalProperties();
        for (final String prop: additionalProperties) {
            res += StringUtils.addSpace(ExtendedPrologStrings.COMMENT) + prop
                    + System.lineSeparator();
        }
        res += "%" + System.lineSeparator();
        res += StringUtils.addSpace(ExtendedPrologStrings.COMMENT)
                + ExtendedPrologStrings.COMPOSITION_RULE_HEADER + System.lineSeparator();
        for (final CompositionRule rule: this.compositionRules) {
            res += rule.toEplString() + System.lineSeparator();
        }
        return res;
    }

    @Override
    public String toString() {
        return this.sessionName;
    }

    /**
     * Creates an extensive string representation of this.
     *
     * @return the string representation
     */
    public String toVerboseString() {
        final StringBuilder res = new StringBuilder(StringUtils.EMPTY);
        res.append("ComponentTypes:" + System.lineSeparator());
        for (final ComponentType ct: this.componentTypes) {
            res.append(StringUtils.indentWithTab(ct.toString() + System.lineSeparator()));
        }
        res.append(System.lineSeparator());
        res.append("Components:" + System.lineSeparator());
        for (final Component c: this.components) {
            res.append(StringUtils.indentWithTab(c.toString() + System.lineSeparator()));
        }
        res.append(System.lineSeparator());
        res.append("ComposableModules:" + System.lineSeparator());
        for (final ComposableModule cm: this.composableModules) {
            res.append(StringUtils.indentWithTab(cm.toString() + System.lineSeparator()));
        }
        res.append(System.lineSeparator());
        res.append("CompositionalStructures:" + System.lineSeparator());
        for (final CompositionalStructure cs: this.compositionalStructures) {
            res.append(StringUtils.indentWithTab(cs.toString() + System.lineSeparator()));
        }
        res.append(System.lineSeparator());
        res.append("Property:" + System.lineSeparator());
        for (final Property p: this.properties) {
            res.append(StringUtils.indentWithTab(p.toString() + System.lineSeparator()));
        }
        res.append(System.lineSeparator());
        res.append("CompositionRules:" + System.lineSeparator());
        for (final CompositionRule cr: this.compositionRules) {
            res.append(StringUtils.indentWithTab(cr.toString() + System.lineSeparator()));
        }
        res.append(System.lineSeparator());
        return res.toString();
    }

    private synchronized void updateFile() {
        final String newContent = this.toEplString();
        final SimpleFileWriter writer = new SimpleFileWriter();
        writer.writeToFile(this.absolutePath, newContent);
    }
}
