package com.fr2501.virage.types;

import java.util.HashSet;
import java.util.Set;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

/**
 * 
 * The data model required to represent the compositional framework as a whole
 * <p>
 * It is designed for the electoral module framework, but not at all limited to it.
 *
 */
public class FrameworkRepresentation {
	private Logger logger = LogManager.getLogger(FrameworkRepresentation.class);
	
	private Set<ComponentType> componentTypes;
	private Set<Component> components;
	private Set<ComposableModule> composableModules;
	private Set<CompositionalStructure> compositionalStructures;
	private Set<CompositionRule> compositionRules;
	private Set<Property> properties;
	
	public FrameworkRepresentation() {
		this.componentTypes = new HashSet<ComponentType>();
		this.components = new HashSet<Component>();
		this.composableModules = new HashSet<ComposableModule>();
		this.compositionalStructures = new HashSet<CompositionalStructure>();
		this.compositionRules = new HashSet<CompositionRule>();
		this.properties = new HashSet<Property>();
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

	public Set<CompositionRule> getCompositionRules() {
		return this.compositionRules;
	}

	public Set<Property> getProperties() {
		return this.properties;
	}
	
	/**
	 * Adds a @link{ComponentType} to the FrameworkRepresentation.
	 * @param ct the @link{ComponentType} to be added
	 */
	public void add(ComponentType ct) {
		this.componentTypes.add(ct);
	}
	
	/**
	 * Adds a @link{Component} to the FrameworkRepresentation.
	 * Performs type check without throwing any exceptions.
	 * @param c the @link{Component} to be added
	 */
	public void add(Component c) {
		this.checkTypes(c);
		this.components.add(c);
	}
	
	/**
	 * Adds a @link{ComposableModule} to the FrameworkRepresentation
	 * Performs type check without throwing any exceptions.
	 * @param cm the @link{ComposableModule} to be added
	 */
	public void add(ComposableModule cm) {
		this.checkTypes(cm);
		this.composableModules.add(cm);
	}
	
	/**
	 * Adds a @link{CompositionalStructure} to the FrameworkRepresentation
	 * Performs type check without throwing any exceptions.
	 * @param cs the @link{CompositionalStructure} to be added
	 */
	public void add(CompositionalStructure cs) {
		this.checkTypes(cs);
		this.compositionalStructures.add(cs);
	}
	
	/**
	 * Adds a @link{CompositionRule} to the FrameworkRepresentation
	 * @param cr the @link{ComposiotionRule} to be added
	 */
	public void add(CompositionRule cr) {
		this.compositionRules.add(cr);
	}
	
	/**
	 * Adds a @link{Property} to the FrameworkRepresentation
	 * Performs type check without throwing any exceptions.
	 * @param ct the @link{Property} to be added
	 */
	public void add(Property p) {
		this.checkTypes(p);
		this.properties.add(p);
	}
	
	@Override
	public String toString() {
		String res = "";
		
		res += "ComponentTypes:\n";
		for(ComponentType ct: this.componentTypes) {
			res += "\t" + ct.toString() + "\n";
		}
		res += "\n";
		
		res += "Components:\n";
		for(Component c: this.components) {
			res += "\t" + c.toString() + "\n";
		}
		res += "\n";
		
		res += "ComposableModules:\n";
		for(ComposableModule cm: this.composableModules) {
			res += "\t" + cm.toString() + "\n";
		}
		res += "\n";
		
		res += "CompositionalStructures:\n";
		for(CompositionalStructure cs: this.compositionalStructures) {
			res += "\t" + cs.toString() + "\n";
		}
		res += "\n";
		
		res += "Property:\n";
		for(Property p: this.properties) {
			res += "\t" + p.toString() + "\n";
		}
		res += "\n";
		
		res += "CompositionRules:\n";
		for(CompositionRule cr: this.compositionRules) {
			res += "\t" + cr.toString() + "\n";
		}
		res += "\n";
		
		return res;
	}

	private void checkTypes(TypedAndParameterized object) {
		this.checkTypes((Typed) object);
		this.checkTypes((Parameterized) object); 
	}
	
	private void checkTypes(Typed object) {
		ComponentType type = object.getType();
		
		if(!this.componentTypes.contains(type)) {
			logger.warn("Added item with unknown type \"" + type.getName() + "\" to framework.");
		}
	}
	
	private void checkTypes(Parameterized object) {
		for(ComponentType paramType: object.getParameters()) {
			if(!this.componentTypes.contains(paramType)) {
				logger.warn("Added item with unknown parameter type \"" + paramType.getName() + "\" to framework.");
			}
		}
	}
} 
