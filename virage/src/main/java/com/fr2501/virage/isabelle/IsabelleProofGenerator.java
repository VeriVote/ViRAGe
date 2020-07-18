package com.fr2501.virage.isabelle;

import java.io.File;
import java.io.IOException;

import com.fr2501.util.SimpleFileReader;
import com.fr2501.virage.types.CompositionProof;

public class IsabelleProofGenerator {
	private static String PROOF_TEMPLATE = "";
	
	public IsabelleProofGenerator() {
		if(PROOF_TEMPLATE.equals("")) {
			SimpleFileReader reader = new SimpleFileReader();
			
			String theoryTemplate = this.getClass().getClassLoader().getResource("theory.template").getFile();
			
			try {
				PROOF_TEMPLATE = reader.readFile(new File(theoryTemplate));
			} catch (IOException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
		}
	}
	
	public String generateIsabelleProof(CompositionProof proof) {
		return proof.toString();
	}
}
