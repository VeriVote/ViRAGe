package com.fr2501.virage.prolog;

import com.fr2501.util.SimpleFileReader;
import com.fr2501.util.StringUtils;
import com.fr2501.virage.types.Component;
import com.fr2501.virage.types.ComponentType;
import com.fr2501.virage.types.ComposableModule;
import com.fr2501.virage.types.CompositionRule;
import com.fr2501.virage.types.CompositionalStructure;
import com.fr2501.virage.types.FrameworkRepresentation;
import com.fr2501.virage.types.Property;
import java.io.File;
import java.io.IOException;
import java.util.LinkedList;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

/**
 * A very simple implementation of the {@link ExtendedPrologParser}.
 *
 */
public class SimpleExtendedPrologParser implements ExtendedPrologParser {
  SimpleFileReader fileReader;
  private final PrologParser prologParser;
  private final Logger logger = LogManager.getLogger(SimpleExtendedPrologParser.class);

  /**
   * Simple constructor.
   */
  public SimpleExtendedPrologParser() {
    logger.info("Initialising SimpleExtendedPrologParser.");

    this.fileReader = new SimpleFileReader();
    this.prologParser = new SimplePrologParser();
  }

  @Override
  public FrameworkRepresentation parseFramework(File file, boolean addDummies)
      throws IOException, MalformedEplFileException {
    List<String> framework = this.fileReader.readFileByLine(file);

    return this.parseFramework(framework, file.getAbsolutePath(), addDummies);
  }

  /**
   * This method does the actual parsing.

   * @param representation a line-by-line representation of the extended Prolog file.
   * @param path the path to the framework (required for compatibility reasons)
   * @return a {@link FrameworkRepresentation} of the input.
   * @throws MalformedEplFileException if the input does not follow the specification of the
   *         extended Prolog format.
   */
  private FrameworkRepresentation parseFramework(List<String> representation, String path,
      boolean addDummies) throws MalformedEplFileException {
    FrameworkRepresentation framework = new FrameworkRepresentation(path);
    framework.setTheoryPath("undefined");
    
    ParserState state = ParserState.STARTING;

    List<String> compositionTypeSection = new LinkedList<String>();
    List<String> composableModuleSection = new LinkedList<String>();
    List<String> compositionalStructureSection = new LinkedList<String>();
    List<String> propertySection = new LinkedList<String>();
    List<String> compositionRuleSection = new LinkedList<String>();

    for (int lineNumber = 0; lineNumber < representation.size(); lineNumber++) {
      String currentLine = representation.get(lineNumber);

      // Skip comments
      if (currentLine.startsWith("%%")) {
        continue;
      }
      
      if (currentLine.contains(ExtendedPrologStrings.THEORY_PATH_PREFIX)) {
        String line = currentLine;

        if (line.contains(" - ")) {
          String[] splits = line.split(" - ");

          line = splits[0];
          framework.setSessionName(splits[1]);
        }

        line = line.replace(ExtendedPrologStrings.THEORY_PATH_PREFIX, "");
        line = line.replace(ExtendedPrologStrings.COMMENT, "");
        line = StringUtils.removeWhitespace(line);

        framework.setTheoryPath(line);
        continue;
      }

      // Remove Prolog comment markings, they are not necessary any more.
      currentLine = currentLine.replace("% ", "");
      currentLine = currentLine.replace("%", "");

      // Skip empty lines. (Careful: currentLine is not actually sanitized after
      // this!)
      if (this.sanitizeLine(currentLine).equals("")) {
        continue;
      }

      state = this.newState(currentLine, state);

      switch (state) {
        case COMPOSITION_TYPE:
          compositionTypeSection.add(currentLine);
          break;
        case COMPOSABLE_MODULE:
          composableModuleSection.add(currentLine);
          break;
        case COMPOSITIONAL_STRUCTURE:
          compositionalStructureSection.add(currentLine);
          break;
        case PROPERTY:
          propertySection.add(currentLine);
          break;
        case COMPOSITION_RULE:
          compositionRuleSection.add(currentLine);
          break;
        default: // no-op, invalid call.
      }
    }

    this.parseSection(framework, compositionTypeSection, ParserState.COMPOSITION_TYPE);
    this.parseSection(framework, composableModuleSection, ParserState.COMPOSABLE_MODULE);
    this.parseSection(framework, compositionalStructureSection,
        ParserState.COMPOSITIONAL_STRUCTURE);
    this.parseSection(framework, propertySection, ParserState.PROPERTY);
    this.parseSection(framework, compositionRuleSection, ParserState.COMPOSITION_RULE);

    if (addDummies) {
      framework.addDummyRulesIfNecessary();
    }

    return framework;
  }

  private void parseSection(FrameworkRepresentation framework, List<String> lines,
      ParserState state) throws MalformedEplFileException {
    switch (state) {
      case COMPOSITION_TYPE:
        this.parseCompositionTypeSection(framework, lines);
        break;
      case COMPOSABLE_MODULE:
      case COMPOSITIONAL_STRUCTURE:
      case PROPERTY:
        this.parseSimpleSection(framework, lines, state);
        break;
      case COMPOSITION_RULE:
        this.parseCompositionRuleSection(framework, lines);
        break;
      default: // no-op, invalid call.
    }
  }

  private void parseCompositionTypeSection(FrameworkRepresentation framework, List<String> lines)
      throws MalformedEplFileException {
    ComponentType currentType = null;

    // Starting at 1, because first line has to be the header by construction.
    for (int i = 1; i < lines.size(); i++) {
      String currentLine = lines.get(i);

      if (currentLine.startsWith("==")) {
        // New type.
        currentLine = this.sanitizeLine(currentLine);
        currentType = new ComponentType(currentLine);
        framework.add(currentType);
      } else {
        // New Instance of given type.
        if (currentType == null) {
          logger.error("No type defined for \"" + currentLine + "\".");
          throw new MalformedEplFileException();
        }

        currentLine = this.sanitizeLine(currentLine);

        List<ComponentType> parameters = this.extractParameters(currentLine);
        currentLine = this.removeBracketExpression(currentLine);

        framework.add(new Component(currentType, currentLine, parameters));
      }
    }
  }

  private void parseSimpleSection(FrameworkRepresentation framework, List<String> lines,
      ParserState state) throws MalformedEplFileException {
    String header = lines.get(0);
    ComponentType type = null;

    // Composable modules are the core component of the framework, the type shall be
    // renameable.
    if (state == ParserState.COMPOSABLE_MODULE) {
      String[] splits = header.split("-");

      if (splits.length > 1) {
        if (splits.length == 2) {
          // Alias is defined, this shall be a type.
          String typeString = this.sanitizeLine(splits[1]);
          type = new ComponentType(typeString);
          framework.setAlias(typeString);
        } else {
          logger.error("Malformed header: \"" + lines.get(0) + "\"");
          throw new MalformedEplFileException();
        }
      } else {
        // Default type.
        type = new ComponentType(ExtendedPrologStrings.COMPOSABLE_MODULE);
      }

      framework.add(type);
    }

    // Starting at 1 due to header.
    for (int i = 1; i < lines.size(); i++) {
      String name = lines.get(i);

      List<ComponentType> parameters = this.extractParameters(name);
      name = this.removeBracketExpression(name);

      switch (state) {
        case COMPOSABLE_MODULE:
          framework.add(new ComposableModule(type, name, parameters));
          break;
        case COMPOSITIONAL_STRUCTURE:
          framework.add(new CompositionalStructure(name, type, parameters));
          break;
        case PROPERTY:
          framework.add(new Property(name, parameters));
          break;
        default: // no-op, invalid call.
      }
    }
  }

  private void parseCompositionRuleSection(FrameworkRepresentation framework, List<String> lines)
      throws MalformedEplFileException {
    String origin = "";
    String name = "";
    String prologString = "";

    // Starting at 1, because of header.
    for (int i = 1; i < lines.size(); i++) {
      String currentLine = lines.get(i);

      if (origin.equals("")) {
        // No origin.
        if (!currentLine.startsWith("=")) {
          logger.error("No origin specified for: \"" + currentLine + "\"");
          throw new MalformedEplFileException();
        } else {
          origin = this.sanitizeLine(currentLine);
          continue;
        }
      } else {
        if (name.equals("")) {
          // No name.
          name = this.sanitizeLine(currentLine);
          continue;
        } else {
          // Origin and name set, looking for Prolog clause now.
          prologString += currentLine;

          if (currentLine.contains(".")) {
            // Clause finished. Start Prolog Parser.

            PrologClause clause = this.prologParser.parseSingleClause(prologString);
            framework.add(new CompositionRule(name, origin, clause));

            origin = "";
            name = "";
            prologString = "";
          }
        }
      }
    }
  }

  private List<ComponentType> extractParameters(String component) throws MalformedEplFileException {
    List<ComponentType> res = new LinkedList<ComponentType>();

    if (!component.contains("(") || component.endsWith("()")) {
      // No parameters.
      return res;
    }

    // Opening, but no closing bracket.
    if (!component.contains(")")) {
      logger.error("Opening, but no closing bracket on: \"" + component + "\"");
      throw new MalformedEplFileException();
    }

    String regex = "\\(.*\\)";
    Pattern pattern = Pattern.compile(regex);
    Matcher matcher = pattern.matcher(component);

    if (matcher.find()) {
      String parameterString = matcher.group();

      // Remove whitespace.
      parameterString = parameterString.replace(" ", "");
      // Get rid of parentheses.
      parameterString = parameterString.substring(1, parameterString.length() - 1);

      String[] parameters = parameterString.split(",");
      for (int i = 0; i < parameters.length; i++) {
        res.add(new ComponentType(parameters[i]));
      }
    } else {
      // This should never happen.
      throw new MalformedEplFileException();
    }

    return res;
  }

  private String removeBracketExpression(String string) {
    String regex = "\\(.*\\)";
    Pattern pattern = Pattern.compile(regex);
    Matcher matcher = pattern.matcher(string);

    if (matcher.find()) {
      String parameterString = matcher.group();
      // Remove parameters from component for simpler processing in calling method.
      string = string.replace(parameterString, "");
    }

    return string;
  }

  private ParserState newState(String line, ParserState oldState) {
    if (line.contains(ExtendedPrologStrings.COMPOSITION_TYPE_HEADER)) {
      return ParserState.COMPOSITION_TYPE;
    }

    if (line.contains(ExtendedPrologStrings.COMPOSABLE_MODULE_HEADER)) {
      return ParserState.COMPOSABLE_MODULE;
    }

    if (line.contains(ExtendedPrologStrings.COMPOSITIONAL_STRUCTURE_HEADER)) {
      return ParserState.COMPOSITIONAL_STRUCTURE;
    }

    if (line.contains(ExtendedPrologStrings.PROPERTY_HEADER)) {
      return ParserState.PROPERTY;
    }

    if (line.contains(ExtendedPrologStrings.COMPOSITION_RULE_HEADER)) {
      return ParserState.COMPOSITION_RULE;
    }

    return oldState;
  }

  private String sanitizeLine(String line) {
    String res = line.replaceAll("=", "");
    res = StringUtils.removeWhitespace(res);

    return res;
  }
}
