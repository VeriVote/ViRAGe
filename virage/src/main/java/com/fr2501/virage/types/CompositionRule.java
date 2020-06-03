package com.fr2501.virage.types;

import java.util.Collection;

public class CompositionRule {
	private String name;
	private String origin;
	private Property succedent;
	private Collection<Property> antecedents;
	
	public CompositionRule(String name, String origin, Property succedent, Collection<Property> antecedents) {
		this.name = name;
		this.origin = origin;
		this.succedent = succedent;
		this.antecedents = antecedents;
	}
	
	public String getName() {
		return this.name;
	}
	public String getOrigin() {
		return this.origin;
	}
	public Property getSuccedent() {
		return this.succedent;
	}
}
