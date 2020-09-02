package com.fr2501.virage.isabelle;

import java.io.File;
import java.io.IOException;
import java.util.List;
import java.util.Map;

import com.fr2501.util.SimpleFileReader;
import com.fr2501.util.SimpleFileWriter;
import com.fr2501.util.StringUtils;
import com.fr2501.virage.types.FrameworkRepresentation;

// TODO: Document
public class IsabelleCodeGenerator {
	private static final String CODE = "_code";
	private static final String END = "end";
	
	private final FrameworkRepresentation framework;
	private final IsabelleTheoryParser parser;
	private final SimpleFileReader reader;
	
	private final String exportTemplate;
	private static final String MODULE_NAME_VAR = "$MODULE_NAME";
	private static final String LANGUAGE_VAR = "$LANGUAGE";
	
	public IsabelleCodeGenerator(FrameworkRepresentation framework) throws IOException {
		this.framework = framework;
		
		this.reader = new SimpleFileReader();
		this.parser = new IsabelleTheoryParser();
		
		this.exportTemplate = this.reader.readFile(new File(this.getClass().getClassLoader().getResource("export_code.template").getFile()));
	}
	
	public File generateCode(File theory, String language) throws IOException {
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
		
		return null;
	}
}
