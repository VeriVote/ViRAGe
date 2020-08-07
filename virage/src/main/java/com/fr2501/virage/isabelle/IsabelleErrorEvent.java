package com.fr2501.virage.isabelle;

import java.util.Map;

/**
 * 
 * Is raised whenever the Isabelle CLI throws errors
 *
 */
public class IsabelleErrorEvent extends IsabelleEvent {

	public IsabelleErrorEvent(Map<String, String> parameters) {
		super(parameters);
	}

}
