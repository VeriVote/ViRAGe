package com.fr2501.virage.types;

import java.util.HashSet;
import java.util.Set;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

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

	public void add(ComponentType ct) {
		this.componentTypes.add(ct);
	}
	
	public void add(Component c) {
		this.checkTypes(c);
		this.components.add(c);
	}
	
	public void add(ComposableModule cm) {
		this.checkTypes(cm);
		this.composableModules.add(cm);
	}
	
	public void add(CompositionalStructure cs) {
		this.checkTypes(cs);
		this.compositionalStructures.add(cs);
	}
	
	public void add(CompositionRule cr) {
		this.compositionRules.add(cr);
	}
	
	public void add(Property p) {
		this.checkTypes(p);
		this.properties.add(p);
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
