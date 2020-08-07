package com.fr2501.virage.isabelle;

import java.util.HashMap;
import java.util.Map;

/**
 * 
 * An {@link IsabelleEvent} raised whenever none of the concrete types fits the event.
 *
 */
public class IsabelleMiscEvent extends IsabelleEvent {
	public IsabelleMiscEvent() {
		super(new HashMap<String, String>());
	}
	
	public IsabelleMiscEvent(Map<String, String> parameters) {
		super(parameters);
	}

}
