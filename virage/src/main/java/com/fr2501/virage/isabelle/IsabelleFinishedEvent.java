package com.fr2501.virage.isabelle;

import java.util.Map;

// TODO Document
public class IsabelleFinishedEvent extends IsabelleEvent {

	public IsabelleFinishedEvent(Map<String, String> parameters) {
		super(parameters);
	}

	@Override
	public void applyEffects(IsabelleProofChecker checker) {
		checker.setFinished(true);
	}
}
