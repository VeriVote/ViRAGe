package com.fr2501.virage.isabelle;

import java.io.File;
import java.io.IOException;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import com.fr2501.util.SimpleFileReader;
import com.fr2501.util.StringUtils;
import com.fr2501.virage.types.CompositionProof;
import com.fr2501.virage.types.CompositionalStructure;
import com.fr2501.virage.types.FrameworkRepresentation;

// TODO: Document
public class IsabelleTheoryGenerator {
	private static final String VAR_THEORY_NAME = "$THEORY_NAME";
	private static final String VAR_IMPORTS = "$IMPORTS";
	private static final String VAR_MODULE_NAME = "$MODULE_NAME";
	private static final String VAR_MODULE_DEF = "$MODULE_DEF";
	private static final String VAR_PROOFS = "$PROOFS";
	
	private static final String THEORY_NAME = "generated_theory";
	private static final String MODULE_NAME = "Generated_module";
	
	private static String THEORY_TEMPLATE = "";
	private static int theoryCounter = 0;
	
	private FrameworkRepresentation framework;
	private Set<String> functionsAndDefinitions;
	
	private IsabelleProofGenerator generator;
	
	public IsabelleTheoryGenerator(FrameworkRepresentation framework, String theoryPath) {
		if(THEORY_TEMPLATE.equals("")) {
			SimpleFileReader reader = new SimpleFileReader();
			
			String theoryTemplate = this.getClass().getClassLoader().getResource("theory.template").getFile();
			
			try {
				THEORY_TEMPLATE = reader.readFile(new File(theoryTemplate));
			} catch (IOException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
		}
		
		this.framework = framework;
		this.generator = new IsabelleProofGenerator();
		
		IsabelleTheoryParser parser = new IsabelleTheoryParser();
		
		try {
			this.functionsAndDefinitions = parser.getAllFunctionsAndDefinitions(theoryPath);
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}
	
	public void generateTheoryFile(String path, String composition, List<CompositionProof> proofs) {
		String theoryName = THEORY_NAME + "_" + theoryCounter;
		String moduleName = MODULE_NAME + "_" + theoryCounter;
		
		String imports = this.findImports(proofs);
		String moduleDef = this.translatePrologToIsabelle(composition);
		
		String proofsString = "";
		for(CompositionProof proof: proofs) {
			proofsString += this.generator.generateIsabelleProof(proof) + "\n\n";
		}
		
		String fileContents = this.replaceVariables(theoryName, imports, moduleName, moduleDef, proofsString);
	}
	
	private String findImports(List<CompositionProof> proofs) {
		String res = "";
		
		Set<String> origins = new HashSet<String>();
		for(CompositionProof proof: proofs) {
			origins.addAll(proof.getAllOrigins());
		}
		
		boolean usingUnprovenFacts = false;
		Set<String> originStrings = new HashSet<String>();
		for(String origin: origins) {
			if(origin.contains(".thy")) {
				// Isabelle expects imports without suffix.
				originStrings.add(origin.replace(".thy", ""));
			} else {
				// Proof relies on unproven facts, add a comment explaining this.
				usingUnprovenFacts = true;
			}
		}
		
		res = StringUtils.printCollection(originStrings);
		// Isabelle expects imports to be space separated.
		res = res.replace(",", " ");
		
		if(usingUnprovenFacts) {
			res += "\n\n"
					+ "(* * * * * * * * * * * * * * * * * * * * * * * *)\n"
					+ "(* Some proofs appear to rely on facts not yet *)\n"
					+ "(*  proven within Isabelle/HOL. Check Isabelle *)\n"
					+ "(*     error messages for more information.    *)\n"
					+ "(* * * * * * * * * * * * * * * * * * * * * * * *)";
		}
		
		return res;
	}
	
	// This method tries, along with other things, to match Prolog predicates
	// to Isabelle entities. It is case-insensitive, so no two Isabelle entities
	// may share the same name with different capitalization.
	private String translatePrologToIsabelle(String prologString) {
		String res = prologString.replace(",", ")(");
		res = res.replace("(", " (");
		
		Pattern pattern = Pattern.compile("[a-zA-Z_]+");
		Matcher matcher = pattern.matcher(res);
	
		while(matcher.find()) {
			System.out.println(res.substring(matcher.start(), matcher.end()));
			String match = res.substring(matcher.start(), matcher.end());
			String replacement = match;
			
			for(String string: this.functionsAndDefinitions) {
				if(string.equalsIgnoreCase(match)) {
					replacement = string;
					break;
				}
			}

			res = res.replace(match, replacement);
		}
		
		return res;
	}
	
	private String replaceVariables(String theoryName, String imports, 
			String moduleName, String moduleDef, String proofs) {
		String res = THEORY_TEMPLATE;
		
		res = res.replace(VAR_THEORY_NAME, theoryName);
		res = res.replace(VAR_IMPORTS, imports);
		res = res.replace(VAR_MODULE_NAME, moduleName);
		res = res.replace(VAR_MODULE_DEF, moduleDef);
		res = res.replace(VAR_PROOFS, proofs);
		
		return res;
	}
}
