package com.fr2501.virage.types;

import java.util.HashSet;
import java.util.Set;

public class FrameworkRepresentation {
	private Set<ComponentType> componentTypes;
	private Set<ComposableModule> composableModules;
	private Set<CompositionalStructure> compositionalStructures;
	private Set<CompositionRule> compositionRules;
	private Set<Property> properties;
	
	public FrameworkRepresentation() {
		this.componentTypes = new HashSet<ComponentType>();
		this.composableModules = new HashSet<ComposableModule>();
		this.compositionalStructures = new HashSet<CompositionalStructure>();
		this.compositionRules = new HashSet<CompositionRule>();
		this.properties = new HashSet<Property>();
	}
	
	public void addComponentType(ComponentType ct) {
		this.componentTypes.add(ct);
	}
	
	public void addComposableModule(ComposableModule cm) {
		this.composableModules.add(cm);
	}
	
	public void addCompositionalStructure(CompositionalStructure cs) {
		this.compositionalStructures.add(cs);
	}
	
	public void addCompositionRule(CompositionRule cr) {
		this.compositionRules.add(cr);
	}
	
	public void addProperty(Property p) {
		this.properties.add(p);
	}
} 
