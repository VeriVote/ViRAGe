package com.fr2501.virage.types;

import java.util.List;

public class Property extends FrameworkComponent {
	private String origin;
	
	public Property(String name, String type, List<FrameworkComponent> parameters) {
		super(name, type, parameters);
	}
	
	public String getOrigin() {
		return this.origin;
	}
}
