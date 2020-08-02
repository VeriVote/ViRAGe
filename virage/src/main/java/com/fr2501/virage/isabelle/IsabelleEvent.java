package com.fr2501.virage.isabelle;

import java.util.Map;

public abstract class IsabelleEvent {
	private Map<String, String> parameters;
	
	public IsabelleEvent(Map<String, String> parameters) {
		this.parameters = parameters;
	}
	
	public String getValue(String key) {
		return this.parameters.get(key);
	}
	
	public void applyEffects(IsabelleProofChecker observer) {
		// default: no-op
	}
	
	@Override
	public String toString() {
		String res = this.getClass().getCanonicalName();
		
		for(String key: this.parameters.keySet()) {
			res += "\n\t" + key + ": " + this.parameters.get(key);
		}
		
		return res;
	}
}
