package com.fr2501.virage.core;

import java.util.LinkedList;
import java.util.List;

// TODO: Document
public class VirageJob {
	private VirageJobType type;
	private List<String> arguments;
	
	public VirageJob(VirageJobType type, String argument) {
		this.type = type;
		this.arguments = new LinkedList<String>();
		this.arguments.add(argument);
	}
	
	public VirageJob(VirageJobType type, List<String> arguments) {
		this.type = type;
		this.arguments = arguments;
	}
	
	public VirageJobType getType() {
		return this.type;
	}
	
	public List<String> getArguments() {
		return this.arguments;
	}
}
