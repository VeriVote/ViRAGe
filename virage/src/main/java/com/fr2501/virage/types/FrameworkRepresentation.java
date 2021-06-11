package com.fr2501.virage.types;

import com.fr2501.util.Pair;
import com.fr2501.util.SimpleFileWriter;
import com.fr2501.virage.core.ConfigReader;
import com.fr2501.virage.prolog.PrologClause;
import com.fr2501.virage.prolog.PrologPredicate;
import java.util.Collections;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

/**
 * The data model required to represent the compositional framework as a whole
 * <p>
 * It is designed for the electoral module framework, but not at all limited to it.
 *
 */
public class FrameworkRepresentation {
  private Logger logger = LogManager.getLogger(FrameworkRepresentation.class);

  private String absolutePath;
  private String theoryPath;
  private String sessionName;

  private Set<ComponentType> componentTypes;
  private Set<Component> components;
  private Set<ComposableModule> composableModules;
  private Set<CompositionalStructure> compositionalStructures;
  private List<CompositionRule> compositionRules;
  private Set<Property> properties;

  private List<Pair<String, String>> typeSynonyms;
  private List<ComponentType> atomicTypes;

  private String composableModuleAlias;

  /*
   * public FrameworkRepresentation() { this(null); }
   */

  public FrameworkRepresentation(String absolutePath) {
    this.absolutePath = absolutePath;

    this.componentTypes = new HashSet<ComponentType>();
    this.components = new HashSet<Component>();
    this.composableModules = new HashSet<ComposableModule>();
    this.compositionalStructures = new HashSet<CompositionalStructure>();
    this.compositionRules = new LinkedList<CompositionRule>();
    this.properties = new HashSet<Property>();
  }

  public String getAbsolutePath() {
    return this.absolutePath;
  }

  public void setAbsolutePath(String absolutePath) {
    this.absolutePath = absolutePath;
  }

  public Set<ComponentType> getComponentTypes() {
    return this.componentTypes;
  }

  public Set<Component> getComponents() {
    return this.components;
  }

  public Set<ComposableModule> getComposableModules() {
    return this.composableModules;
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

  public List<Pair<String, String>> getTypeSynonyms() {
    return typeSynonyms;
  }

  public void setTypeSynonyms(List<Pair<String, String>> typeSynonyms) {
    this.typeSynonyms = typeSynonyms;
  }

  public String getAlias() {
    return this.composableModuleAlias;
  }

  public void setTheoryPath(String theoryPath) {
    this.theoryPath = theoryPath;
  }

  public String getTheoryPath() {
    return this.theoryPath;
  }

  public void setSessionName(String sessionName) {
    this.sessionName = sessionName;
  }

  public String getSessionName() {
    return this.sessionName;
  }

  public void setAlias(String alias) {
    this.composableModuleAlias = alias;
  }

  /**
   * Returns the {@link Property} with the given name.
   * 
   * @param name the name
   * @return the {@link Property}, null if it does not exist.
   */
  public Property getProperty(String name) {
    for (Property property : this.properties) {
      if (property.getName().equals(name)) {
        return property;
      }
    }

    return null;
  }

  /**
   * Returns the {@link ComposableModule} with the given name.
   * 
   * @param name the name
   * @return the {@link ComposableModule}, null if it does not exist.
   */
  public ComposableModule getComposableModule(String name) {
    for (ComposableModule module : this.composableModules) {
      if (module.getName().equals(name)) {
        return module;
      }
    }

    return null;
  }

  /**
   * Returns the {@link CompositionalStructure} with the given name.
   * 
   * @param name the name
   * @return the {@link CompositionalStructure}, null if it does not exist.
   */
  public CompositionalStructure getCompositionalStructure(String name) {
    for (CompositionalStructure component : this.compositionalStructures) {
      if (component.getName().equals(name)) {
        return component;
      }
    }

    return null;
  }

  /**
   * Returns the {@link Component} with the given name.
   * 
   * @param name the name
   * @return the {@link Component}, null if it does not exist.
   */
  public Component getComponent(String name) {
    for (Component component : this.components) {
      if (component.getName().equals(name)) {
        return component;
      }
    }

    for (ComposableModule module : this.composableModules) {
      if (module.getName().equals(name)) {
        return module;
      }
    }

    return null;
  }

  /**
   * Adds a @link{ComponentType} to the FrameworkRepresentation.
   * 
   * @param ct the @link{ComponentType} to be added
   */
  public void add(ComponentType ct) {
    this.componentTypes.add(ct);
  }

  /**
   * Adds a @link{Component} to the FrameworkRepresentation. Performs type check without throwing
   * any exceptions.
   * 
   * @param c the @link{Component} to be added
   */
  public void add(Component c) {
    this.checkTypes(c);
    this.components.add(c);
  }

  /**
   * Adds a @link{ComposableModule} to the FrameworkRepresentation Performs type check without
   * throwing any exceptions.
   * 
   * @param cm the @link{ComposableModule} to be added
   */
  public void add(ComposableModule cm) {
    this.checkTypes(cm);
    this.composableModules.add(cm);
  }

  /**
   * Adds a @link{CompositionalStructure} to the FrameworkRepresentation Performs type check without
   * throwing any exceptions.
   * 
   * @param cs the @link{CompositionalStructure} to be added
   */
  public void add(CompositionalStructure cs) {
    this.checkTypes(cs);
    this.compositionalStructures.add(cs);
  }

  /**
   * Adds a @link{CompositionRule} to the FrameworkRepresentation.
   * 
   * @param cr the @link{ComposiotionRule} to be added
   */
  public void add(CompositionRule cr) {
    /*
     * PrologClause actualClause = this.removeAtomicTypesFromClause(cr.getClause()); if(actualClause
     * == null) { return; }
     * 
     * cr = new CompositionRule(cr.getName(), cr.getOrigin(), actualClause);
     */

    for (CompositionRule rule : this.compositionRules) {
      if (rule.equals(cr)) {
        return;
      }
    }

    this.compositionRules.add(cr);
  }

  /**
   * Adds a {@link Property} to the FrameworkRepresentation Performs type check without throwing any
   * exceptions.
   * 
   * @param p the {@link Property} to be added
   */
  public void add(Property p) {
    this.checkTypes(p);
    this.properties.add(p);
  }

  public void addDummyRulesIfNecessary() {
    List<String> atomicTypeStrings = ConfigReader.getInstance().getAtomicTypes();
    this.atomicTypes = new LinkedList<ComponentType>();
    for (String s : atomicTypeStrings) {
      ComponentType type = new ComponentType(s);
      this.add(type);
      this.atomicTypes.add(type);
    }

    for (Property p : this.properties) {
      boolean allAtomicTypes = true;
      for (ComponentType type : p.getParameters()) {
        if (!this.atomicTypes.contains(type)) {
          allAtomicTypes = false;
          break;
        }
      }

      if (allAtomicTypes) {
        // A new rule is added such that the atomic properties are ignored.
        List<PrologPredicate> params = new LinkedList<PrologPredicate>();
        for (int i = 0; i < p.getParameters().size(); i++) {
          params.add(new PrologPredicate("_"));
        }

        PrologPredicate pred = new PrologPredicate(p.getName(), params);
        PrologClause clause = new PrologClause(pred);

        CompositionRule rule = new CompositionRule(p.getName() + "_intro", "generated", clause);
        this.add(rule);

        this.updateFile();
      }
    }
  }

  @Override
  public String toString() {
    return this.sessionName;
  }

  public String toVerboseString() {
    String res = "";

    res += "ComponentTypes:\n";
    for (ComponentType ct : this.componentTypes) {
      res += "\t" + ct.toString() + "\n";
    }
    res += "\n";

    res += "Components:\n";
    for (Component c : this.components) {
      res += "\t" + c.toString() + "\n";
    }
    res += "\n";

    res += "ComposableModules:\n";
    for (ComposableModule cm : this.composableModules) {
      res += "\t" + cm.toString() + "\n";
    }
    res += "\n";

    res += "CompositionalStructures:\n";
    for (CompositionalStructure cs : this.compositionalStructures) {
      res += "\t" + cs.toString() + "\n";
    }
    res += "\n";

    res += "Property:\n";
    for (Property p : this.properties) {
      res += "\t" + p.toString() + "\n";
    }
    res += "\n";

    res += "CompositionRules:\n";
    for (CompositionRule cr : this.compositionRules) {
      res += "\t" + cr.toString() + "\n";
    }
    res += "\n";

    return res;
  }

  public String toEplString() {
    Collections.sort(this.compositionRules);

    String res = "";

    res += "% ==== " + this.theoryPath + " - " + this.sessionName + "\n";

    res += "%\n";

    res += "% === component_type\n";
    for (ComponentType type : this.componentTypes) {
      res += "% == " + type.getName() + "\n";
      for (Component comp : this.components) {
        if (comp.getType().equals(type)) {
          res += "% " + comp.toStringWithoutTypeSignature() + "\n";
        }
      }
    }

    res += "%\n";

    res += "% === composable_module\n";

    res += "%% This area is deprecated and therefore intentionally empty.\n";

    res += "% === compositional_structure\n";
    for (CompositionalStructure structure : this.compositionalStructures) {
      res += "% " + structure.toString() + "\n";
    }

    res += "%\n";

    res += "% === property\n";
    for (Property prop : this.properties) {
      res += "% " + prop.toString() + "\n";
    }
    List<String> additionalProperties = ConfigReader.getInstance().getAdditionalProperties();
    for (String prop : additionalProperties) {
      res += "% " + prop + "\n";
    }

    res += "%\n";

    res += "% === composition_rule\n";
    for (CompositionRule rule : this.compositionRules) {
      res += rule.toEplString() + "\n";
    }

    return res;
  }

  private void checkTypes(TypedAndParameterized object) {
    this.checkTypes((Typed) object);
    this.checkTypes((Parameterized) object);
  }

  private void checkTypes(Typed object) {
    ComponentType type = object.getType();

    if (!this.componentTypes.contains(type)) {
      logger.info("Added item with unknown type \"" + type.getName() + "\" to framework.");
    }
  }

  private void checkTypes(Parameterized object) {
    for (ComponentType paramType : object.getParameters()) {
      if (!this.componentTypes.contains(paramType)) {
        logger.info(
            "Added item with unknown parameter type \"" + paramType.getName() + "\" to framework.");
      }
    }
  }

  private synchronized void updateFile() {
    String newContent = this.toEplString();

    SimpleFileWriter writer = new SimpleFileWriter();
    writer.writeToFile(this.absolutePath, newContent);
  }
}
