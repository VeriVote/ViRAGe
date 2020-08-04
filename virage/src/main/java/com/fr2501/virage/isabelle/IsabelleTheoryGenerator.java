package com.fr2501.virage.isabelle;

import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.io.StringWriter;
import java.nio.charset.StandardCharsets;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.apache.commons.io.IOUtils;

import com.fr2501.util.SimpleFileReader;
import com.fr2501.util.SimpleFileWriter;
import com.fr2501.util.StringUtils;
import com.fr2501.virage.prolog.PrologParser;
import com.fr2501.virage.prolog.PrologPredicate;
import com.fr2501.virage.prolog.SimplePrologParser;
import com.fr2501.virage.types.Component;
import com.fr2501.virage.types.ComponentType;
import com.fr2501.virage.types.CompositionProof;
import com.fr2501.virage.types.FrameworkRepresentation;

// TODO: Document
public class IsabelleTheoryGenerator {
	private static final String VAR_THEORY_NAME = "$THEORY_NAME";
	private static final String VAR_IMPORTS = "$IMPORTS";
	private static final String VAR_MODULE_PARAM_TYPES = "$MODULE_PARAM_TYPES";
	protected static final String VAR_MODULE_NAME = "$MODULE_NAME";
	protected static final String VAR_MODULE_PARAMETERS = "$MODULE_PARAMETERS";
	private static final String VAR_MODULE_DEF = "$MODULE_DEF";
	private static final String VAR_ASSUMPTIONS = "$ASSUMPTIONS";
	private static final String VAR_PROOFS = "$PROOFS";
	
	private static final String THEORY_NAME = "generated_theory";
	private static final String MODULE_NAME = "Generated_module";
	private static final String RIGHT_ARROW = " => ";
	private static final String TYPE = "'a ";
	
	// TODO Find better solution
	private static final String ASSUMES = "assumes";
	private static final String LINEAR_ORDER = "linear_order";
	private static final String REL = "rel";
	private static final String TRUE = "true";
	
	private static String THEORY_TEMPLATE = "";
	private static int theoryCounter = 0;
	private Map<String, String> functionsAndDefinitions;
	private FrameworkRepresentation framework;
	
	private IsabelleProofGenerator generator;
	private PrologParser parser;
	
	private Map<String, String> typedVariables;
	
	public IsabelleTheoryGenerator(String theoryPath, FrameworkRepresentation framework) {
		if(THEORY_TEMPLATE.equals("")) {
			InputStream theoryTemplateStream = this.getClass().getClassLoader().getResourceAsStream("theory.template");
			StringWriter writer = new StringWriter();
			try {
				IOUtils.copy(theoryTemplateStream, writer, StandardCharsets.UTF_8);
			} catch (IOException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
			THEORY_TEMPLATE = writer.toString();
		}

		IsabelleTheoryParser parser = new IsabelleTheoryParser();
		
		try {
			this.functionsAndDefinitions = parser.getAllFunctionsAndDefinitions(theoryPath);
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		
		this.framework = framework;
		this.generator = new IsabelleProofGenerator(this.framework, this, this.functionsAndDefinitions);
		this.parser = new SimplePrologParser();
		this.typedVariables = new HashMap<String, String>();
	}
	
	// If path points to a file, this file will be overwritten and the name will most probably
	// not correspond to the theory inside, so Isabelle won't be able to verify it.
	public File generateTheoryFile(String path, String composition, List<CompositionProof> proofs) {
		String theoryName = THEORY_NAME + "_" + theoryCounter;
		String moduleName = MODULE_NAME + "_" + theoryCounter;
		theoryCounter++;
		
		PrologPredicate proofPredicate = this.parser.parsePredicate(composition);
		this.replacePrologVariables(proofPredicate);
		String moduleParameters = "";
		
		// This looks tedious, but is required to ensure correct 
		// ordering of variables in definition.
		// This assumes that variable names are given in the correct order,
		// ascending alphabetically. This might seem arbitrary, but is ensured
		// by the way IsabelleUtils.findUnusedVariables works.
		List<String> moduleParametersList = new LinkedList<String>();
		for (String type: this.typedVariables.keySet()) {
			moduleParametersList.add(this.typedVariables.get(type));
		}
		
		Collections.sort(moduleParametersList);
		for(String param: moduleParametersList) {
			moduleParameters += " " + param;
		}
		
		List<String> moduleParamTypesList = new LinkedList<String>();
		for(int i=0; i<moduleParametersList.size(); i++) {
			for(String type: this.typedVariables.keySet()) {
				if(this.typedVariables.get(type).equals(moduleParametersList.get(i))) {
					String moduleParamType = "";
					// Simple types like nat don't require an "'a".
					if(!IsabelleUtils.isSimpleType(type)) {
						moduleParamType = TYPE;
					}
					
					moduleParamType += type + RIGHT_ARROW;
					moduleParamTypesList.add(i, moduleParamType);
				}
			}
		}
			
		String moduleParamTypes = "";
		for(String type: moduleParamTypesList) {
			moduleParamTypes += type;
		}
		// -----
			
		String assumptions = ASSUMES + " \"" + TRUE + "\"";
		// TODO: This is terribly ugly, but it's the best I can do for now.
		if(this.typedVariables.keySet().contains(REL)) {
			assumptions = ASSUMES + " " + "\"" + LINEAR_ORDER + " " + this.typedVariables.get(REL) + "\"";
		}
		
		String imports = this.findImportsFromCompositionRules(proofs);
		
		Map<String, Set<String>> moduleDefMap = IsabelleUtils.translatePrologToIsabelle(this.functionsAndDefinitions, proofPredicate);
		if(moduleDefMap.keySet().size() != 1) {
			throw new IllegalArgumentException();
		}
		
		// There will be only one iteration, but it is a bit tedious to extract
		// single elements from sets.
		String moduleDef = "";
		for(String string: moduleDefMap.keySet()) {
			moduleDef = string;
			
			// Additional imports might have occured, which are only relevant
			// for the definition of the module, but not used within the proofs.
			// Add those.
			for(String importString: moduleDefMap.get(string)) {
				String importStringWithoutSuffix = importString.replace(".thy", "");
				
				if(!imports.contains(importStringWithoutSuffix)) {
					imports += " " + importStringWithoutSuffix + " ";
				}
			}
		}
		
		String proofsString = "";
		for(CompositionProof proof: proofs) {
			proofsString += this.generator.generateIsabelleProof(proof) + "\n\n";
		}
		
		String fileContents = this.replaceVariables(theoryName, imports, moduleParamTypes,
				moduleName, moduleParameters, moduleDef, assumptions, proofsString);
		
		SimpleFileWriter writer = new SimpleFileWriter();
		
		try {
			File file = new File(path).getCanonicalFile();
			
			// If the path points to a folder, create a new file.
			if(file.isDirectory()) {
				path = path + theoryName + ".thy";
			}
			writer.writeToFile(path, fileContents);
			
			return new File(path).getCanonicalFile();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		
		return null;
	}
	
	protected void replacePrologVariables(PrologPredicate predicate) {
		for(int i=0; i<predicate.getParameters().size(); i++) {
			PrologPredicate child = predicate.getParameters().get(i);
			if(child.isVariable()) {
				System.out.println(child.getName());
				
				Component component = framework.getComponent(predicate.getName());
				ComponentType childType = component.getParameters().get(i);
				
				if(!this.typedVariables.containsKey(childType.getName())) {
					this.typedVariables.put(childType.getName(), IsabelleUtils.getUnusedVariable(predicate.toString()));
				} 
				
				child.setName(this.typedVariables.get(childType.getName()));
			}
			
			this.replacePrologVariables(child);
		}
	}
	
	private String findImportsFromCompositionRules(List<CompositionProof> proofs) {
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
	
	private String replaceVariables(String theoryName, String imports, String moduleParamTypes,
			String moduleName, String moduleParameters, String moduleDef, String assumptions, String proofs) {
		String res = THEORY_TEMPLATE;
		
		res = res.replace(VAR_PROOFS, proofs);
		
		res = res.replace(VAR_THEORY_NAME, theoryName);
		res = res.replace(VAR_IMPORTS, imports);
		res = res.replace(VAR_MODULE_PARAM_TYPES, moduleParamTypes);
		res = res.replace(VAR_MODULE_DEF, moduleDef);
		
		res = res.replace(VAR_MODULE_NAME, moduleName);
		res = res.replace(VAR_MODULE_PARAMETERS, moduleParameters);
		res = res.replace(VAR_ASSUMPTIONS, assumptions);
		
		System.out.println(res);
		return res;
	}
}
