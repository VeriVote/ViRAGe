package com.fr2501.virage.types;

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

import com.fr2501.util.Pair;
import com.fr2501.util.SimpleFileWriter;
import com.fr2501.util.StringUtils;
import com.fr2501.virage.core.ConfigReader;
import com.fr2501.virage.core.VirageCore;
import com.fr2501.virage.prolog.ExtendedPrologStrings;
import com.fr2501.virage.prolog.PrologClause;
import com.fr2501.virage.prolog.PrologParser;
import com.fr2501.virage.prolog.PrologPredicate;
import com.fr2501.virage.prolog.SimplePrologParser;

/**
 * The data model required to represent the compositional framework as a whole It is designed for
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
    private static final String SEPARATOR = "%%%%%%%%%%%%%%%%%%%%\n";

    /**
     * Path to the (E)PL file.
     */
    private String absolutePath;
    /**
     * Path to Isabelle theories.
     */
    private String theoryPath;
    /**
     * Name of the Isabelle sesison.
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
     * Set of composable modules.
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
     * Composable module alias.
     */
    @Deprecated
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
     *
     * @param cs the @link{CompositionalStructure} to be added
     */
    @Deprecated
    public void add(final CompositionalStructure cs) {
        // this.checkTypes(cs);
        this.compositionalStructures.add(cs);
    }

    /**
     * Adds a @link{CompositionRule} to the FrameworkRepresentation.
     *
     * @param cr the @link{ComposiotionRule} to be added
     */
    public void add(final CompositionRule cr) {
        /*
         * PrologClause actualClause = this.removeAtomicTypesFromClause(cr.getClause());
         * if(actualClause == null) { return; }
         *
         * cr = new CompositionRule(cr.getName(), cr.getOrigin(), actualClause);
         */

        for (final CompositionRule rule : this.compositionRules) {
            if (rule.equals(cr)) {
                return;
            }
        }

        this.compositionRules.add(cr);
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

        for (final Property p : this.properties) {
            for (int i = 0; i < p.getArity(); i++) {

                final ComponentType propertyType = p.getParameters().get(i);

                int aliasIdx = 0;
                for (final String alias : aliases.keySet()) {
                    final PrologPredicate aliasPredicate = parser.parsePredicate(alias);
                    final String aliasName = aliasPredicate.getName();
                    final Component aliasComponent = this.getComponent(aliasName);

                    if (aliasComponent != null && !aliasComponent.getType().equals(propertyType)) {
                        continue;
                    }

                    final List<PrologPredicate> newSuccParams = new LinkedList<PrologPredicate>();
                    final List<PrologPredicate> newAnteParams = new LinkedList<PrologPredicate>();
                    final String nextFreeVariable = "ALIAS_VAR_";
                    for (int j = 0; j < p.getArity(); j++) {
                        if(i == j) {
                            newSuccParams.add(parser.parsePredicate(alias));
                            newAnteParams.add(parser.parsePredicate(aliases.get(alias)));
                        } else {
                            newSuccParams.add(new PrologPredicate(nextFreeVariable + j));
                            newAnteParams.add(new PrologPredicate(nextFreeVariable + j));
                        }
                    }

                    final PrologPredicate newSucc = new PrologPredicate(p.getName(), newSuccParams);
                    final PrologPredicate newAnte = new PrologPredicate(p.getName(), newAnteParams);

                    final PrologClause clause = new PrologClause(newSucc, newAnte);
                    final CompositionRule rule = new CompositionRule(
                            p.getName() + "_alias_" + aliasIdx, ExtendedPrologStrings.ASSUMPTION,
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
        for (final String s : atomicTypeStrings) {
            final ComponentType type = new ComponentType(s);
            this.add(type);
            this.atomicTypes.add(type);
        }

        for (final Property p : this.properties) {
            boolean allAtomicTypes = true;
            for (final ComponentType type : p.getParameters()) {
                if (!this.atomicTypes.contains(type)) {
                    allAtomicTypes = false;
                    break;
                }
            }

            if (allAtomicTypes) {
                // A new rule is added such that the atomic properties are ignored.
                final List<PrologPredicate> params = new LinkedList<PrologPredicate>();
                for (int i = 0; i < p.getParameters().size(); i++) {
                    params.add(new PrologPredicate("_"));
                }

                p.setAtomic(true);

                final PrologPredicate pred = new PrologPredicate(p.getName(), params);
                final PrologClause clause = new PrologClause(pred);

                final CompositionRule rule = new CompositionRule(p.getName() + "_intro",
                        "ASSUMPTION", clause);
                this.add(rule);

                this.updateFile();
            }
        }
    }

    private void checkTypes(final Parameterized object) {
        for (final ComponentType paramType : object.getParameters()) {
            if (!this.componentTypes.contains(paramType)) {
                LOGGER.info("Added item with unknown parameter type \"" + paramType.getName()
                        + "\" to framework.");
            }
        }
    }

    private void checkTypes(final Typed object) {
        final ComponentType type = object.getType();

        if (!this.componentTypes.contains(type)) {
            LOGGER.info("Added item with unknown type \"" + type.getName() + "\" to framework.");
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

        res += "%% Generated by ViRAGe " + VirageCore.getVersion() + " at " + dtf.format(now)
                + ".\n";

        res += SEPARATOR;

        res += "%% To add new composition rules, go to the bottom of this file.\n"
                + "%% A rule definition consists of three parts. "
                + "The first one represents its origin,\n"
                + "%% for user defined rules this will always be \"UNPROVEN\". The second part is\n"
                + "%% the symbolic name of the rule that will be used in generated proofs.\n"
                + "%% The third part is a Prolog clause capturing the semantics of the rule.\n"
                + "%%\n" + "%% Example:\n" + "%% % = UNPROVEN\n"
                + "%% % example_rule_without_meaning\n" + "%% property_a(X) :- property_b(X).\n";

        res += SEPARATOR;

        return res;

    }

    public String getAbsolutePath() {
        return this.absolutePath;
    }

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
        for (final Component component : this.components) {
            if (component.getName().equals(name)) {
                return component;
            }
        }

        for (final ComposableModule module : this.composableModules) {
            if (module.getName().equals(name)) {
                return module;
            }
        }

        return null;
    }

    public Set<Component> getComponents() {
        return this.components;
    }

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
        for (final ComposableModule module : this.composableModules) {
            if (module.getName().equals(name)) {
                return module;
            }
        }

        return null;
    }

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
        for (final CompositionalStructure component : this.compositionalStructures) {
            if (component.getName().equals(name)) {
                return component;
            }
        }

        return null;
    }

    public Set<CompositionalStructure> getCompositionalStructures() {
        return this.compositionalStructures;
    }

    public List<CompositionRule> getCompositionRules() {
        return this.compositionRules;
    }

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
        for (final Property property : this.properties) {
            if (property.getName().equals(name)) {
                return property;
            }
        }

        return null;
    }

    public String getSessionName() {
        return this.sessionName;
    }

    public String getTheoryPath() {
        return this.theoryPath;
    }

    public List<Pair<String, String>> getTypeSynonyms() {
        return this.typeSynonyms;
    }

    public void setAbsolutePath(final String newAbsolutePath) {
        this.absolutePath = newAbsolutePath;
    }

    public void setAlias(final String alias) {
        this.composableModuleAlias = alias;
    }

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

        res += "% ==== " + this.theoryPath + "ROOT" + " - " + this.sessionName
                + System.lineSeparator();

        res += ExtendedPrologStrings.COMMENT + System.lineSeparator();

        res += ExtendedPrologStrings.COMMENT + StringUtils.SPACE
                + ExtendedPrologStrings.COMPOSITION_TYPE_HEADER + System.lineSeparator();
        for (final ComponentType type : this.componentTypes) {
            res += "% == " + type.getName() + System.lineSeparator();
            for (final Component comp : this.components) {
                if (comp.getType().equals(type)) {
                    res += ExtendedPrologStrings.COMMENT + StringUtils.SPACE
                            + comp.toStringWithoutTypeSignature() + System.lineSeparator();
                }
            }
        }

        res += ExtendedPrologStrings.COMMENT + System.lineSeparator();

        /*
         * res += "% === composable_module\n"; res +=
         * "%% This area is deprecated and therefore intentionally empty.\n";
         *
         * res += "% === compositional_structure\n"; res +=
         * "%% This area is deprecated and therefore intentionally empty.\n";
         *
         * res += "%\n";
         */

        res += ExtendedPrologStrings.COMMENT + StringUtils.SPACE
                + ExtendedPrologStrings.PROPERTY_HEADER + System.lineSeparator();
        for (final Property prop : this.properties) {
            res += ExtendedPrologStrings.COMMENT + StringUtils.SPACE + prop.toString()
                    + System.lineSeparator();
        }
        final List<String> additionalProperties = ConfigReader.getInstance()
                .getAdditionalProperties();
        for (final String prop : additionalProperties) {
            res += ExtendedPrologStrings.COMMENT + StringUtils.SPACE + prop
                    + System.lineSeparator();
        }

        res += "%\n";

        res += ExtendedPrologStrings.COMMENT + StringUtils.SPACE
                + ExtendedPrologStrings.COMPOSITION_RULE_HEADER + System.lineSeparator();
        for (final CompositionRule rule : this.compositionRules) {
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
        String res = "";

        res += "ComponentTypes:\n";
        for (final ComponentType ct : this.componentTypes) {
            res += StringUtils.indentWithTab(ct.toString() + System.lineSeparator());
        }
        res += System.lineSeparator();

        res += "Components:\n";
        for (final Component c : this.components) {
            res += StringUtils.indentWithTab(c.toString() + System.lineSeparator());
        }
        res += System.lineSeparator();

        res += "ComposableModules:\n";
        for (final ComposableModule cm : this.composableModules) {
            res += StringUtils.indentWithTab(cm.toString() + System.lineSeparator());
        }
        res += System.lineSeparator();

        res += "CompositionalStructures:\n";
        for (final CompositionalStructure cs : this.compositionalStructures) {
            res += StringUtils.indentWithTab(cs.toString() + System.lineSeparator());
        }
        res += System.lineSeparator();

        res += "Property:\n";
        for (final Property p : this.properties) {
            res += StringUtils.indentWithTab(p.toString() + System.lineSeparator());
        }
        res += System.lineSeparator();

        res += "CompositionRules:\n";
        for (final CompositionRule cr : this.compositionRules) {
            res += StringUtils.indentWithTab(cr.toString() + System.lineSeparator());
        }
        res += System.lineSeparator();

        return res;
    }

    private synchronized void updateFile() {
        final String newContent = this.toEplString();

        final SimpleFileWriter writer = new SimpleFileWriter();
        writer.writeToFile(this.absolutePath, newContent);
    }
}
