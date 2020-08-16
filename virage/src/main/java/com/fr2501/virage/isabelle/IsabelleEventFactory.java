package com.fr2501.virage.isabelle;

import java.io.IOException;
import java.util.HashMap;
import java.util.Map;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import com.fasterxml.jackson.databind.ObjectMapper;

/**
 * 
 * A factory for Isabelle events, parses the Strings given by the Isabelle CLI.
 *
 */
public class IsabelleEventFactory {
	private static final String OK_STRING = "OK";
	private static final String ERROR_STRING = "ERROR";
	private static final String NOTE_STRING = "NOTE";
	private static final String FINISHED_STRING = "FINISHED";
	
	private ObjectMapper mapper;
	
	public IsabelleEventFactory() {
		this.mapper = new ObjectMapper();
	}
	
	/**
	 * Creates an {@link IsabelleEvent} representing the event described within the given String.
	 * @param s the String given by the Isabelle client CLI
	 * @return the corresponding event
	 */
	public IsabelleEvent createEvent(String s) {
		Map<String, String> parameters = this.extractParameters(s);
		
		if(s.startsWith(OK_STRING)) {
			return new IsabelleOkEvent(parameters);
		} else if(s.startsWith(ERROR_STRING)) {
			return new IsabelleErrorEvent(parameters);
		} else if(s.startsWith(NOTE_STRING)) {
			return new IsabelleNoteEvent(parameters);
		} else if(s.startsWith(FINISHED_STRING)) {
			return new IsabelleFinishedEvent(parameters);
		}
		
		return new IsabelleMiscEvent();
	}
	
	private Map<String, String> extractParameters(String s) {
		Map<String,String> res = new HashMap<String,String>();
		Pattern pattern = Pattern.compile("\\{.*\\}");
		Matcher matcher = pattern.matcher(s);
		
		if(matcher.find()) {
			String paramString = s.substring(matcher.start(), matcher.end());
			
			try {
				Map<?,?> map = this.mapper.readValue(paramString, Map.class);
				
				for(Object o: map.keySet()) {
					res.put(o.toString(), map.get(o).toString());
				}
				
				return res;
			} catch (IOException e) {
				// This should never happen.
				return null;
			}
		} else {
			return new HashMap<String, String>();
		}
	}
}
