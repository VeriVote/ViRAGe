package com.fr2501.virage.prolog;

import java.io.File;
import java.io.IOException;
import java.util.LinkedList;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import com.fr2501.util.SimpleFileReader;
import com.fr2501.virage.types.Component;
import com.fr2501.virage.types.ComponentType;
import com.fr2501.virage.types.ComposableModule;
import com.fr2501.virage.types.FrameworkRepresentation;

public class SimpleExtendedPrologParser implements ExtendedPrologParser {
	SimpleFileReader fileReader;
	private final PrologParser prologParser;
	private final Logger logger = LogManager.getLogger(SimpleExtendedPrologParser.class);
	
	public SimpleExtendedPrologParser() {
		this.fileReader = new SimpleFileReader();
		this.prologParser = new SimplePrologParser();
	}
	
	@Override
	public FrameworkRepresentation parseFramework(File file) throws IOException, MalformedEPLFileException {
		logger.trace("parseFramework(" + file.getAbsolutePath().toString() + ")");
		
		List<String> framework = this.fileReader.readFileByLine(file);
		
		return this.parseFramework(framework);
	}

	private FrameworkRepresentation parseFramework(List<String> representation) throws MalformedEPLFileException {
		logger.trace("parseFramework(representation)");
		
		FrameworkRepresentation framework = new FrameworkRepresentation();
		ParserState state = ParserState.STARTING;
		
		List<String> compositionTypeSection = new LinkedList<String>();
		List<String> composableModuleSection = new LinkedList<String>();
		List<String> compositionalStructureSection = new LinkedList<String>();
		List<String> propertySection = new LinkedList<String>();
		List<String> compositionRuleSection = new LinkedList<String>();
		
		for(int lineNumber=0; lineNumber<representation.size(); lineNumber++) {
			String currentLine = representation.get(lineNumber);
			
			// Skip comments
			if(currentLine.startsWith("%%")) continue;
			
			// Remove Prolog comment markings, they are not necessary any more.
			currentLine = currentLine.replace("% ", "");
			currentLine = currentLine.replace("%", "");
			
			// Skip empty lines. (Careful: currentLine is not actually sanitized after this!)
			if(this.sanitizeLine(currentLine).equals("")) continue;
			
			state = this.newState(currentLine, state);
			
			switch(state) {
			case COMPOSITION_TYPE: 			compositionTypeSection.add(currentLine); 		break;
			case COMPOSABLE_MODULE: 		composableModuleSection.add(currentLine); 		break;
			case COMPOSITIONAL_STRUCTURE: 	compositionalStructureSection.add(currentLine); break;
			case PROPERTY: 					propertySection.add(currentLine); 				break;
			case COMPOSITION_RULE: 			compositionRuleSection.add(currentLine); 		break;
			default: 						throw new MalformedEPLFileException();
			}
		}
		
		this.parseSection(framework, compositionTypeSection, ParserState.COMPOSITION_TYPE);
		this.parseSection(framework, composableModuleSection, ParserState.COMPOSABLE_MODULE);
		this.parseSection(framework, compositionalStructureSection, ParserState.COMPOSITIONAL_STRUCTURE);
		this.parseSection(framework, propertySection, ParserState.PROPERTY);
		this.parseSection(framework, compositionRuleSection, ParserState.COMPOSITION_RULE);
		
		return framework;
	}
	
	private void parseSection(FrameworkRepresentation framework, List<String> lines, ParserState state) throws MalformedEPLFileException {
		switch(state) {
		case COMPOSITION_TYPE: this.parseCompositionTypeSection(framework, lines); break;
		case COMPOSABLE_MODULE: case COMPOSITIONAL_STRUCTURE: case PROPERTY: this.parseSimpleSection(framework, lines, state); break;
		case COMPOSITION_RULE: this.parseCompositionRuleSection(framework, lines); break;
		default: // no-op, invalid call.
		}
	}
	
	@SuppressWarnings("unused")
	private void parseCompositionTypeSection(FrameworkRepresentation framework, List<String> lines) throws MalformedEPLFileException {
		// Starting at 1, because first line has to be the header by construction.
		for(int i=1; i<lines.size(); i++) {
			String currentLine = lines.get(i);
			ComponentType currentType = null;
			
			if(currentLine.startsWith("==")) {
				// New type.
				currentLine = this.sanitizeLine(currentLine);
				currentType = new ComponentType(currentLine);
				framework.addComponentType(currentType);
			} else {
				// New Instance of given type.
				if(currentType == null) {
					throw new MalformedEPLFileException();
				}
				
				// Eclipse claims these lines to be dead, they are not.
				currentLine = this.sanitizeLine(currentLine);
				
				List<ComponentType> parameters = this.extractParameters(currentLine);
				
				framework.addComponent(new Component(currentType, currentLine, parameters));
			}
		}
	}
	
	private void parseSimpleSection(FrameworkRepresentation framework, List<String> lines, ParserState state) throws MalformedEPLFileException {
		// Has to be there by construction.
		String header = lines.get(0);
		String[] splits = header.split("-");
		ComponentType type = null;
		
		if(splits.length > 1) {
			if(splits.length == 2) {
				// Alias is defined, this shall be a type.
				String typeString = this.sanitizeLine(splits[1]);
				type = new ComponentType(typeString);
				framework.addComponentType(type);
			} else {
				throw new MalformedEPLFileException();
			}
		} else {
			// Default type.
			switch(state) {
			case COMPOSABLE_MODULE: type = new ComponentType(ExtendedPrologStrings.COMPOSABLE_MODULE); break;
			default: // no-op, invalid call.
			}

		}
		
		// Starting at 1 due to header.
		for(int i=1; i<lines.size(); i++) {
			String module = lines.get(i);
			
			List<ComponentType> parameters = this.extractParameters(module);
			
			switch(state) {
			case COMPOSABLE_MODULE: framework.addComposableModule(new ComposableModule(type, module, parameters)); break;
			default: // no-op, invalid call.
			}
		}
	}
	
	private void parseCompositionRuleSection(FrameworkRepresentation framework, List<String> lines) throws MalformedEPLFileException {
		String origin = "";
		String name = "";
		String prologString = "";
		
		// Starting at 1, because of header.
		for(int i=1; i<lines.size(); i++) {
			String currentLine = lines.get(i);
			
			if(origin.equals("")) {
				// No origin.
				if(!currentLine.startsWith("=")) {
					throw new MalformedEPLFileException();
				} else {
					origin = this.sanitizeLine(currentLine);
					continue;
				}
			} else {
				if(name.equals("")) {
					// No name.
					name = this.sanitizeLine(currentLine);
					continue;
				} else {
					// Origin and name set, looking for Prolog clause now.
					if(currentLine.contains(".")) {
						// Clause finished. Start Prolog Parser.
						prologString = prologString.replace("\n", "");
						
						PrologClause clause = this.prologParser.parseSingleClause(prologString);
						// TODO: translate clause
						
					} else {
						prologString += currentLine;
					}
				}
			}
		}
	}
	
	private List<ComponentType> extractParameters(String component) throws MalformedEPLFileException {
		List<ComponentType> res = new LinkedList<ComponentType>();
		
		if(!component.contains("(")) {
			// No brackets, so no parameters.
			return res;
		}
		
		// Opening, but no closing bracket.
		if(!component.contains(")")) {
			throw new MalformedEPLFileException();
		}
		
		String regex = "\\(.*\\)";
		Pattern pattern = Pattern.compile(regex);
		Matcher matcher = pattern.matcher(component);
		
		if(matcher.find()) {
			String parameterString = matcher.group(1);
			// Remove parameters from component for simpler processing in calling method.
			component = component.replace(parameterString, "");
			
			// Remove whitespace.
			parameterString = parameterString.replace(" ", "");
			// Get rid of parentheses.
			parameterString = parameterString.substring(1, parameterString.length()-1);
			
			String[] parameters = parameterString.split(",");
			for(int i=0; i<parameters.length; i++) {
				res.add(new ComponentType(parameters[i]));
			}
		} else {
			// This should never happen.
			throw new MalformedEPLFileException();
		}
		
		return res;
	}
	
	private ParserState newState(String line, ParserState oldState) {
		if(line.contains(ExtendedPrologStrings.COMPOSITION_TYPE_HEADER)) {
			return ParserState.COMPOSITION_TYPE;
		}
		
		if(line.contains(ExtendedPrologStrings.COMPOSABLE_MODULE_HEADER)) {
			return ParserState.COMPOSABLE_MODULE;
		}
		
		if(line.contains(ExtendedPrologStrings.COMPOSITIONAL_STRUCTURE_HEADER)) {
			return ParserState.COMPOSITIONAL_STRUCTURE;
		}
		
		if(line.contains(ExtendedPrologStrings.PROPERTY_HEADER)) {
			return ParserState.PROPERTY;
		}
		
		if(line.contains(ExtendedPrologStrings.COMPOSITION_RULE_HEADER)) {
			return ParserState.COMPOSITION_RULE;
		}
		
		return oldState;
	}
	
	private String sanitizeLine(String line) {
		String res = line.replaceAll("=", "");
		res = res.replaceAll(" ", "");
		
		return res;
	}
}
