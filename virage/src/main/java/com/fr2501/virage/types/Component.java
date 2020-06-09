package com.fr2501.virage.types;

import java.util.LinkedList;
import java.util.List;

public class Component {
	private ComponentType type;
	private String name;
	private List<ComponentType> parameters;
	
	public Component(ComponentType type, String name, List<ComponentType> parameters) {
		this.type = type;
		this.name = name;
		this.parameters = parameters;
	}
	
	public Component(ComponentType type, String name) {
		this(type, name, new LinkedList<ComponentType>());
	}
	
	public ComponentType getType() {
		return this.type;
	}
	public String getName() {
		return this.name;
	}
	public List<ComponentType> getParameters() {
		return this.parameters;
	}
}
