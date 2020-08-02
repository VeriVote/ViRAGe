package com.fr2501.virage.isabelle;

import java.util.Map;

public class IsabelleFinishedEvent extends IsabelleEvent {

	public IsabelleFinishedEvent(Map<String, String> parameters) {
		super(parameters);
		// TODO Auto-generated constructor stub
	}

	@Override
	public void applyEffects(IsabelleProofChecker checker) {
		checker.setFinished(true);
	}
}
