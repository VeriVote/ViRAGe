package com.fr2501.virage.types;

import java.util.List;

public abstract class FrameworkComponent {
	protected String name;
	protected String type = "default";
	protected int arity;
	protected List<FrameworkComponent> parameters;
	
	public FrameworkComponent(String name, String type, List<FrameworkComponent> parameters) {
		this.name = name;
		this.type = type;
		this.parameters = parameters;
	}
	
	public String getName() {
		return this.name;
	}
	public String getType() {
		return this.type;
	}
	public int getArity() {
		return this.arity;
	}
	public List<FrameworkComponent> getParameters() {
		return this.parameters;
	}
}
