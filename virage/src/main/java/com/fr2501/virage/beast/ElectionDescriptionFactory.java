package com.fr2501.virage.beast;

import edu.pse.beast.datatypes.electiondescription.ElectionDescription;
import edu.pse.beast.types.cbmctypes.inputplugins.Preference;
import edu.pse.beast.types.cbmctypes.outputplugins.CandidateList;

/**
 * 
 * Generates {@link ElectionDescription}s as required by BEAST
 *
 */
public class ElectionDescriptionFactory {
	public static ElectionDescription getElectionDescriptionFromString(String codeString) {
		ElectionDescription result = new ElectionDescription("test", new Preference(), new CandidateList());
		result.setCode(codeString);
		
		return result;
	}
}
