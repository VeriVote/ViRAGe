package com.fr2501.virage.types;

import java.io.File;
import java.time.ZonedDateTime;
import java.time.format.DateTimeFormatter;
import java.util.Collections;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import com.fr2501.util.Pair;
import com.fr2501.util.SimpleFileWriter;
import com.fr2501.virage.core.ConfigReader;
import com.fr2501.virage.core.VirageCore;
import com.fr2501.virage.prolog.ExtendedPrologStrings;
import com.fr2501.virage.prolog.PrologClause;
import com.fr2501.virage.prolog.PrologPredicate;

/**
 * The data model required to represent the compositional framework as a whole It is designed for
 * the electoral module framework, but not at all limited to it.
 *
 */
public final class FrameworkRepresentation {
    private static final Logger logger = LogManager.getLogger(FrameworkRepresentation.class);

    private static final String SEPARATOR = "%%%%%%%%%%%%%%%%%%%%\n";

    private String absolutePath;
    private String theoryPath;
    private String sessionName;

    private final Set<ComponentType> componentTypes;
    private final Set<Component> components;
    private final Set<ComposableModule> composableModules;
    private final Set<CompositionalStructure> compositionalStructures;
    private final List<CompositionRule> compositionRules;
    private final Set<Property> properties;

    private List<Pair<String, String>> typeSynonyms;
    private List<ComponentType> atomicTypes;

    private String composableModuleAlias;

    /*
     * public FrameworkRepresentation() { this(null); }
     */

    /**
     * Simple constructor.
     *
     * @param absolutePath path to the EPL file
     */
    public FrameworkRepresentation(final String absolutePath) {
        this.absolutePath = absolutePath;

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
     * Adds dummy rules (e.g. ($property)_intro) if these are required.
     */
    public void addDummyRulesIfNecessary() {
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
                logger.info("Added item with unknown parameter type \"" + paramType.getName()
                + "\" to framework.");
            }
        }
    }

    private void checkTypes(final Typed object) {
        final ComponentType type = object.getType();

        if (!this.componentTypes.contains(type)) {
            logger.info("Added item with unknown type \"" + type.getName() + "\" to framework.");
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

    public void setAbsolutePath(final String absolutePath) {
        this.absolutePath = absolutePath;
    }

    public void setAlias(final String alias) {
        this.composableModuleAlias = alias;
    }

    public void setSessionName(final String sessionName) {
        this.sessionName = sessionName;
    }

    public void setTheoryPath(final String theoryPath) {
        String theoryPathCopy = theoryPath;

        if (!theoryPath.endsWith(File.separator)) {
            theoryPathCopy = theoryPath + File.separator;
        }

        this.theoryPath = theoryPathCopy;
    }

    public void setTypeSynonyms(final List<Pair<String, String>> typeSynonyms) {
        this.typeSynonyms = typeSynonyms;
    }

    /**
     * Creates a string representation of this in the EPL format.
     *
     * @return the string representation
     */
    public String toEplString() {
        Collections.sort(this.compositionRules);

        String res = this.createHeader();

        res += "% ==== " + this.theoryPath + "ROOT" + " - " + this.sessionName + "\n";

        res += "%\n";

        res += "% " + ExtendedPrologStrings.COMPOSITION_TYPE_HEADER + "\n";
        for (final ComponentType type : this.componentTypes) {
            res += "% == " + type.getName() + "\n";
            for (final Component comp : this.components) {
                if (comp.getType().equals(type)) {
                    res += "% " + comp.toStringWithoutTypeSignature() + "\n";
                }
            }
        }

        res += "%\n";

        /*
         * res += "% === composable_module\n"; res +=
         * "%% This area is deprecated and therefore intentionally empty.\n";
         *
         * res += "% === compositional_structure\n"; res +=
         * "%% This area is deprecated and therefore intentionally empty.\n";
         *
         * res += "%\n";
         */

        res += "% " + ExtendedPrologStrings.PROPERTY_HEADER + "\n";
        for (final Property prop : this.properties) {
            res += "% " + prop.toString() + "\n";
        }
        final List<String> additionalProperties = ConfigReader.getInstance()
                .getAdditionalProperties();
        for (final String prop : additionalProperties) {
            res += "% " + prop + "\n";
        }

        res += "%\n";

        res += "% " + ExtendedPrologStrings.COMPOSITION_RULE_HEADER + "\n";
        for (final CompositionRule rule : this.compositionRules) {
            res += rule.toEplString() + "\n";
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
            res += "\t" + ct.toString() + "\n";
        }
        res += "\n";

        res += "Components:\n";
        for (final Component c : this.components) {
            res += "\t" + c.toString() + "\n";
        }
        res += "\n";

        res += "ComposableModules:\n";
        for (final ComposableModule cm : this.composableModules) {
            res += "\t" + cm.toString() + "\n";
        }
        res += "\n";

        res += "CompositionalStructures:\n";
        for (final CompositionalStructure cs : this.compositionalStructures) {
            res += "\t" + cs.toString() + "\n";
        }
        res += "\n";

        res += "Property:\n";
        for (final Property p : this.properties) {
            res += "\t" + p.toString() + "\n";
        }
        res += "\n";

        res += "CompositionRules:\n";
        for (final CompositionRule cr : this.compositionRules) {
            res += "\t" + cr.toString() + "\n";
        }
        res += "\n";

        return res;
    }

    private synchronized void updateFile() {
        final String newContent = this.toEplString();

        final SimpleFileWriter writer = new SimpleFileWriter();
        writer.writeToFile(this.absolutePath, newContent);
    }
}
