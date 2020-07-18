package com.fr2501.virage.isabelle;

import java.io.File;
import java.io.IOException;

import com.fr2501.util.SimpleFileReader;

public class IsabelleProofStepGenerator {
	private static String PROOF_STEP_TEMPLATE = "";
	
	public IsabelleProofStepGenerator() {
		if(PROOF_STEP_TEMPLATE.equals("")) {
			SimpleFileReader reader = new SimpleFileReader();
			
			String theoryTemplate = this.getClass().getClassLoader().getResource("theory.template").getFile();
			
			try {
				PROOF_STEP_TEMPLATE = reader.readFile(new File(theoryTemplate));
			} catch (IOException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
		}
	}
}
