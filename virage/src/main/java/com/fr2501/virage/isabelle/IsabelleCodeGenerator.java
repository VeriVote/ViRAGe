package com.fr2501.virage.isabelle;

import java.io.File;
import java.io.IOException;
import java.text.SimpleDateFormat;
import java.util.Date;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import com.fr2501.util.ProcessUtils;
import com.fr2501.util.SimpleFileReader;
import com.fr2501.util.SimpleFileWriter;
import com.fr2501.util.StringUtils;
import com.fr2501.virage.types.CompilationFailedException;
import com.fr2501.virage.types.CompositionProof;
import com.fr2501.virage.types.DecompositionTree;
import com.fr2501.virage.types.FrameworkRepresentation;
import com.fr2501.virage.types.IsabelleBuildFailedException;

/**
 * 
 * This class is used to engage the Isabelle Code Generation process and produce Scala code.
 *
 */
public class IsabelleCodeGenerator {
	private static final Logger logger = LogManager.getLogger(IsabelleCodeGenerator.class);
	
	private static final String CODE = "_code";
	private static final String END = "end";
	
	private final FrameworkRepresentation framework;
	private Map<String,String> codeReplacements;
	
	private final IsabelleTheoryGenerator generator;
	private final IsabelleTheoryParser parser;
	private final SimpleFileReader reader;
	
	private final String exportTemplate;
	private final String rootTemplate;
	private final String votingContextTemplate;
	private static final String MODULE_NAME_VAR = "$MODULE_NAME";
	private static final String LANGUAGE_VAR = "$LANGUAGE";
	private static final String SESSION_NAME_VAR = "$SESSION_NAME";
	private static final String THEORY_NAME_VAR = "$THEORY_NAME";
	private static final String PARAM_VAR = "$PARAMS";
	
	// TODO: This feels too "hard-coded"
	private static final String ENUM = "Enum";
	private static final String ENUM_COMMENT = "ENUM";
	private static final String EQUALITY = "HOL.equal";
	private static final String EQUALITY_COMMENT = "EQUALITY";
	private static final String RELATION = "(x: Set.set[(A, A)]):";
	private static final String OPTION1_COMMENT = "OPTION1";
	private static final String OPTION2_COMMENT = "OPTION2";
	
	public IsabelleCodeGenerator(FrameworkRepresentation framework) throws IOException {
		this.framework = framework;
		
		this.reader = new SimpleFileReader();
		this.parser = new IsabelleTheoryParser();
		this.generator = new IsabelleTheoryGenerator(framework);
		
		this.initCodeReplacements();
		
		this.exportTemplate = this.reader.readFile(new File(this.getClass().getClassLoader().getResource("export_code.template").getFile()));
		this.rootTemplate = this.reader.readFile(new File(this.getClass().getClassLoader().getResource("root.template").getFile()));
		this.votingContextTemplate = this.reader.readFile(new File(this.getClass().getClassLoader().getResource("voting_context.template").getFile()));
	}
	
	// TODO: DOC
	public File generateCode(String composition, IsabelleCGLanguage language) throws IOException, InterruptedException, IsabelleBuildFailedException {
		File theory = this.generator.generateTheoryFile(composition, new LinkedList<CompositionProof>());
		
		return this.generateCode(theory, language);
	}
	
	public File generateCode(DecompositionTree composition, IsabelleCGLanguage language) throws IOException, InterruptedException, IsabelleBuildFailedException {
		return this.generateCode(composition.toString(), language);
	}
	
	public File generateCode(File theory, IsabelleCGLanguage language) throws IOException, InterruptedException, IsabelleBuildFailedException {
		String moduleName = this.prepareTheoryFile(theory, language);
		
		String theoryName = theory.getName().substring(0,
				theory.getName().length() - (IsabelleUtils.FILE_EXTENSION.length()));
		
		String sessionName = this.buildSessionRoot(theoryName, theory);
		
		try {
			File codeFile = this.invokeIsabelleCodeGeneration(theory, sessionName, theoryName);
			
			return codeFile;
		} catch (IsabelleBuildFailedException e) {
			logger.error("Isabelle code generation failed for file " + theory.getCanonicalPath() + ".");
			
			throw e;
		}
	}
	
	/**
	 * Creates an ad-hoc Isabelle session, invokes code generation, attempts to compile the result
	 * and returns an executable jar file if possible.
	 * 
	 * @param composition the composition to be translated to Scala code
	 * @return an executable Scala-jar file
	 * @throws IOException if file system interaction goes wrong
	 * @throws InterruptedException if processes are interrupted prematurely
	 * @throws CompilationFailedException if Scala compilation fails
	 * @throws IsabelleBuildFailedException if Isabelle code generation fails
	 */
	public File generateScalaCodeAndCompile(String composition) throws IOException, InterruptedException, CompilationFailedException, IsabelleBuildFailedException {
		File theory = this.generator.generateTheoryFile(composition, new LinkedList<CompositionProof>());
		
		return this.generateScalaCodeAndCompile(theory);
	}
	
	/**
	 * Creates an ad-hoc Isabelle session, invokes code generation, attempts to compile the result
	 * and returns an executable jar file if possible.
	 * 
	 * @param theory the theory file, containing exactly one definition, on which code generation shall take place
	 * @return an executable Scala-jar file if possible
	 * @throws IOException if file system interaction goes wrong
	 * @throws InterruptedException if processes are interrupted prematurely
	 * @throws CompilationFailedException if Scala compilation fails
	 * @throws IsabelleBuildFailedException if Isabelle code generation fails
	 */
	public File generateScalaCodeAndCompile(File theory) throws IOException, InterruptedException, CompilationFailedException, IsabelleBuildFailedException {
		String moduleName = this.prepareTheoryFile(theory, "Scala");
		
		String theoryName = theory.getName().substring(0,
				theory.getName().length() - (IsabelleUtils.FILE_EXTENSION.length()));
		
		String sessionName = this.buildSessionRoot(theoryName, theory);
		
		File codeFile = this.invokeIsabelleCodeGeneration(theory, sessionName, theoryName);
		
		// First, try using implicit values only
		File votingContext = this.prepareVotingContext(theoryName, moduleName, codeFile, false);
		
		String jarPath = codeFile.getParent() + File.separator + moduleName + ".jar";
		
		int status = ProcessUtils.runTerminatingProcessAndLogOutput(
				"scalac " + codeFile.getCanonicalPath() + " " + votingContext.getCanonicalPath()
				+ " -d " + jarPath);

		if(status != 0) {
			logger.error("Generated Scala code could not be compiled.");
			
			// Implicit values did not work, try setting them explicitly.
			votingContext = this.prepareVotingContext(theoryName, moduleName, codeFile, true);
			
			status = ProcessUtils.runTerminatingProcessAndLogOutput(
					"scalac " + codeFile.getCanonicalPath() + " " + votingContext.getCanonicalPath()
					+ " -d " + jarPath);
			
			if(status != 0) {
				throw new CompilationFailedException();
			}
		}
		
		logger.info("Scala compilation was successful. The jar file can be found at " + jarPath);
		
		return new File(jarPath);
	}
	
	private void initCodeReplacements() throws IOException {
		Map<String,String> replacements = new HashMap<String,String>();
		Map<String,String> functionsAndDefinitions = this.parser.getAllFunctionsAndDefinitions(this.framework.getTheoryPath());
		
		Set<String> names = functionsAndDefinitions.keySet();
		
		for(String name: names) {
			if(names.contains(name + CODE)) {
				replacements.put(name, name + CODE);
			}
		}
		
		this.codeReplacements = replacements;
	}
	
	private String prepareTheoryFile(File theory, IsabelleCGLanguage language) throws IOException {
		return this.prepareTheoryFile(theory, language.toString());
	}
	
	private String prepareTheoryFile(File theory, String language) throws IOException {
		String originalName = "";
		String newName = "";
		
		Map<String,String> map = this.parser.getAllFunctionsAndDefinitions(theory.getCanonicalPath());
		if(map.keySet().size() != 1) {
			throw new IllegalArgumentException();
		}
		
		for(String definition: map.keySet()) {
			originalName = definition;
			newName = definition + CODE;
		}
		
		String originalDefinition = this.parser.getDefinitionByName(originalName, theory);
		
		String newDefinition = originalDefinition.replaceAll(originalName, newName);
		
		for(String old: this.codeReplacements.keySet()) {
			// TODO: This is wrong if names are not prefix free. 
			// This should be fixed if this solution stays permanently,
			// but it is only meant as a temporary fix anyway.
			newDefinition = newDefinition.replaceAll(old, this.codeReplacements.get(old));
		}
		
		String exportCommand = this.exportTemplate.replace(MODULE_NAME_VAR, newName);
		exportCommand = exportCommand.replace(LANGUAGE_VAR, language);
		
		String result = newDefinition + "\n\n" + exportCommand;
		
		List<String> lines = this.reader.readFileByLine(theory);
		
		for(int i=0; i<lines.size(); i++) {
			String line = lines.get(i);
			
			if(StringUtils.removeWhitespace(line).equals(END)) {
				lines.add(i, result);
				break;
			}
		}
		
		SimpleFileWriter writer = new SimpleFileWriter();
		writer.writeToFile(theory.getCanonicalPath(), lines);
		
		return newName;
	}
	
	private String buildSessionRoot(String theoryName, File theory) {
		// Session names MUST be universally unique, as Isabelle seems to be incapable of 
		// rebuilding single sessions without triggering full rebuilds.
		// TODO: Is there a way to do it?
		String sessionName = "ad_hoc_session_" + new SimpleDateFormat("yyyyMMddHHmmss").format(new Date());
		
		String result = this.rootTemplate.replace(SESSION_NAME_VAR, sessionName).replace(THEORY_NAME_VAR, theoryName);
		SimpleFileWriter writer = new SimpleFileWriter();
		writer.writeToFile(theory.getParent() + File.separator + "ROOT", result);
		
		return sessionName;
	}
	
	private File invokeIsabelleCodeGeneration(File theory, String sessionName, String theoryName) throws IOException, InterruptedException, IsabelleBuildFailedException {
		String generatedPath = theory.getParent();
		String theoryPath = new File(this.framework.getTheoryPath()).getCanonicalPath();
		
		String isabelleCommand = "isabelle build -e -D " + generatedPath + " -D " + theoryPath + 
				" -o quick_and_dirty -b " + sessionName;
		
		int status = ProcessUtils.runTerminatingProcessAndLogOutput(isabelleCommand);
		
		if(status != 0) {
			logger.error("Isabelle code generation failed.");
			
			throw new IsabelleBuildFailedException();
		}
		
		String codePath = generatedPath + File.separator + "export" + File.separator + sessionName + "." + theoryName + File.separator + "code" + File.separator;
		File codeDir = new File(codePath);
		File[] generatedFiles = codeDir.listFiles();
		
		// Delete ROOT file, it has served its purpose
		File root = new File(generatedPath + File.separator + "ROOT");
		root.delete();
		
		// Isabelle puts everything into one file when generating Scala and OCaml code
		return generatedFiles[0];
	}
	
	private File prepareVotingContext(String theoryName, String moduleName, File moduleFile,
			boolean setExplicitParameters) throws IOException {
		File dir = moduleFile.getParentFile();
		
		SimpleFileReader reader = new SimpleFileReader();
		String code = reader.readFile(moduleFile);
		
		String result = this.votingContextTemplate.replace(THEORY_NAME_VAR, theoryName)
				.replace(MODULE_NAME_VAR, moduleName);
		
		boolean containsEnum = code.contains(ENUM);
		boolean containsEquality = code.contains(EQUALITY);
		boolean requiresRelation = code.contains(RELATION);
		
		List<String> parameters = new LinkedList<String>();
		
		// Enable the required optional parts of the votingContextTemplate
		if(containsEnum) {
			result = result.replace("/* " + ENUM_COMMENT, "").replace(ENUM_COMMENT + " */", "");
			parameters.add("bounded");
		}
		
		if(containsEquality) {
			result = result.replace("/* " + EQUALITY_COMMENT, "").replace(EQUALITY_COMMENT + " */", "");
			parameters.add("eq");
		}
		
		if(requiresRelation) {
			result = result.replace("/* " + OPTION2_COMMENT, "").replace(OPTION2_COMMENT + " */", "");
		} else {
			result = result.replace("/* " + OPTION1_COMMENT, "").replace(OPTION1_COMMENT + " */", "");
		}
		
		String paramString = "";
		// setExplicitParameters is required for now. Sometimes, Scala uses the implicit values,
		// sometimes they have to be given explicitly, so we want to try both.
		if(!parameters.isEmpty() && setExplicitParameters) {
			paramString = "(" + StringUtils.printCollection(parameters) + ")";
		}
		result = result.replace(PARAM_VAR, paramString);
		
		String path = dir.getCanonicalPath() + File.separator + "votingContext.scala";
		
		SimpleFileWriter writer = new SimpleFileWriter();
		writer.writeToFile(path, result);
		
		return new File(path);
	}
}
