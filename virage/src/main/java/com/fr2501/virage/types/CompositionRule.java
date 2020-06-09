package com.fr2501.virage.types;

import com.fr2501.virage.prolog.PrologClause;

public class CompositionRule {
	private String name;
	private String origin;
	private PrologClause clause;
	
	public CompositionRule(String name, String origin, PrologClause clause) {
		this.name = name;
		this.origin = origin;
		this.clause = clause;
	}
	
	public String getName() {
		return this.name;
	}
	public String getOrigin() {
		return this.origin;
	}
	public PrologClause getClause() {
		return this.clause;
	}
}
