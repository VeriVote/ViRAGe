package com.fr2501.virage.isabelle;

import java.io.BufferedReader;
import java.io.File;
import java.io.IOException;
import java.text.SimpleDateFormat;
import java.util.Date;
import java.util.List;
import java.util.Map;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import com.fr2501.util.ProcessUtils;
import com.fr2501.util.SimpleFileReader;
import com.fr2501.util.SimpleFileWriter;
import com.fr2501.util.StringUtils;
import com.fr2501.virage.types.FrameworkRepresentation;

// TODO: Document
public class IsabelleCodeGenerator {
	private static final Logger logger = LogManager.getLogger(IsabelleCodeGenerator.class);
	
	private static final String CODE = "_code";
	private static final String END = "end";
	
	private final FrameworkRepresentation framework;
	private final IsabelleTheoryParser parser;
	private final SimpleFileReader reader;
	
	private final String exportTemplate;
	private final String rootTemplate;
	private final String votingContextTemplate;
	private static final String MODULE_NAME_VAR = "$MODULE_NAME";
	private static final String LANGUAGE_VAR = "$LANGUAGE";
	private static final String SESSION_NAME_VAR = "$SESSION_NAME";
	private static final String THEORY_NAME_VAR = "$THEORY_NAME";
	
	public IsabelleCodeGenerator(FrameworkRepresentation framework) throws IOException {
		this.framework = framework;
		
		this.reader = new SimpleFileReader();
		this.parser = new IsabelleTheoryParser();
		
		this.exportTemplate = this.reader.readFile(new File(this.getClass().getClassLoader().getResource("export_code.template").getFile()));
		this.rootTemplate = this.reader.readFile(new File(this.getClass().getClassLoader().getResource("root.template").getFile()));
		this.votingContextTemplate = this.reader.readFile(new File(this.getClass().getClassLoader().getResource("voting_context.template").getFile()));
	}
	
	public File generateScalaCode(File theory) throws IOException, InterruptedException {
		String moduleName = this.prepareTheoryFile(theory, "Scala");
		
		String theoryName = theory.getName().substring(0,
				theory.getName().length() - (IsabelleUtils.FILE_EXTENSION.length()));
		
		String sessionName = this.buildSessionRoot(theoryName, theory);
		
		File codeFile = this.invokeIsabelleCodeGeneration(theory, sessionName, theoryName);
		
		File votingContext = this.prepareVotingContext(theoryName, moduleName, codeFile.getParentFile());
		
		int status = ProcessUtils.runTerminatingProcessAndLogOutput(
				"scalac " + codeFile.getCanonicalPath() + " " + votingContext.getCanonicalPath()
				+ " -d " + moduleName + ".jar");

		if(status != 0) {
			logger.error("Generated Scala code could not be compiled.");
		}
		
		return new File(codeFile.getParent() + moduleName + ".jar");
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
		
		// TODO: Replace definitions with code-rewrites if necessary
		String newDefinition = originalDefinition.replaceAll(originalName, newName);
		
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
	
	private File invokeIsabelleCodeGeneration(File theory, String sessionName, String theoryName) throws IOException, InterruptedException {
		String generatedPath = theory.getParent();
		String theoryPath = new File(this.framework.getTheoryPath()).getCanonicalPath();
		
		String isabelleCommand = "isabelle build -e -D " + generatedPath + " -D " + theoryPath + 
				" -o quick_and_dirty -b " + sessionName;
		
		int status = ProcessUtils.runTerminatingProcessAndLogOutput(isabelleCommand);
		
		if(status != 0) {
			logger.error("Isabelle code generation failed.");
			
			return null;
		}
		
		String codePath = generatedPath + File.separator + "export" + File.separator + sessionName + "." + theoryName + File.separator + "code" + File.separator;
		File codeDir = new File(codePath);
		File[] generatedFiles = codeDir.listFiles();
		
		// Delete ROOT file, it has served its purpose
		File root = new File(generatedPath + File.separator + "ROOT");
		root.delete();
		
		// Isabelle puts everything into one file when generating Scala code
		return generatedFiles[0];
	}
	
	private File prepareVotingContext(String theoryName, String moduleName, File dir) throws IOException {
		String result = this.votingContextTemplate.replace(THEORY_NAME_VAR, theoryName)
				.replace(MODULE_NAME_VAR, moduleName);
		String path = dir.getCanonicalPath() + File.separator + "votingContext.scala";
		
		SimpleFileWriter writer = new SimpleFileWriter();
		writer.writeToFile(path, result);
		
		return new File(path);
	}
}
