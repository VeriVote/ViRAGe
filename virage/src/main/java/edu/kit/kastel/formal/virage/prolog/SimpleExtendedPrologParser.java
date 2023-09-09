package edu.kit.kastel.formal.virage.prolog;

import java.io.File;
import java.io.IOException;
import java.util.LinkedList;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import edu.kit.kastel.formal.util.SimpleFileReader;
import edu.kit.kastel.formal.util.StringUtils;
import edu.kit.kastel.formal.virage.isabelle.IsabelleUtils;
import edu.kit.kastel.formal.virage.types.Component;
import edu.kit.kastel.formal.virage.types.ComponentType;
import edu.kit.kastel.formal.virage.types.ComposableModule;
import edu.kit.kastel.formal.virage.types.CompositionRule;
import edu.kit.kastel.formal.virage.types.CompositionalStructure;
import edu.kit.kastel.formal.virage.types.FrameworkRepresentation;
import edu.kit.kastel.formal.virage.types.Property;

/**
 * A very simple implementation of the {@link ExtendedPrologParser}.
 *
 * @author VeriVote
 */
public final class SimpleExtendedPrologParser implements ExtendedPrologParser {
    /**
     * The logger.
     */
    private static final Logger LOGGER = LogManager.getLogger(SimpleExtendedPrologParser.class);

    /**
     * A regular expression that matches any parenthesized term.
     */
    private static final String PARENTH_REGEX = "\\(.*\\)";

    /**
     * The file reader.
     */
    private final SimpleFileReader fileReader;

    /**
     * The Prolog parser.
     */
    private final PrologParser prologParser;

    /**
     * Simple constructor.
     */
    public SimpleExtendedPrologParser() {
        LOGGER.info("Initialising SimpleExtendedPrologParser.");
        this.fileReader = new SimpleFileReader();
        this.prologParser = new SimplePrologParser();
    }

    @Override
    public FrameworkRepresentation parseFramework(final File file, final boolean addDummies)
            throws IOException, MalformedEplFileException {
        final List<String> framework = this.fileReader.readFileByLine(file);
        return this.parseFramework(framework, file.getAbsolutePath(), addDummies);
    }

    /**
     * This method does the actual parsing.
     *
     * @param representation a line-by-line representation of the extended Prolog file.
     * @param path the path to the framework (required for compatibility reasons)
     * @param addDummies true iff dummy rules shall be added as specified in settings file
     * @return a {@link FrameworkRepresentation} of the input.
     * @throws MalformedEplFileException if the input does not follow the specification of the
     *      extended Prolog format.
     */
    private FrameworkRepresentation parseFramework(final List<String> representation,
                                                   final String path, final boolean addDummies)
                                                           throws MalformedEplFileException {
        final FrameworkRepresentation framework = new FrameworkRepresentation(path);
        framework.setTheoryPath("undefined");
        ParserState state = ParserState.STARTING;

        final List<String> compositionTypeSection = new LinkedList<String>();
        final List<String> composableModuleSection = new LinkedList<String>();
        final List<String> compositionalStructureSection = new LinkedList<String>();
        final List<String> propertySection = new LinkedList<String>();
        final List<String> compositionRuleSection = new LinkedList<String>();

        for (int lineNumber = 0; lineNumber < representation.size(); lineNumber++) {
            String currentLine = representation.get(lineNumber);
            // Skip comments
            if (currentLine.startsWith("%%")) {
                continue;
            }
            if (currentLine.contains(ExtendedPrologStrings.THEORY_PATH_PREFIX)) {
                this.findTheoryPath(currentLine, framework);
            }
            // Remove Prolog comment markings, they are not necessary any more.
            currentLine = currentLine.replace("% ", StringUtils.EMPTY);
            currentLine = currentLine.replace("%", StringUtils.EMPTY);
            // Skip empty lines. (Careful: currentLine is not actually sanitized after
            // this!)
            if (this.sanitizeLine(currentLine).equals(StringUtils.EMPTY)) {
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
            default: // skip operation, invalid call.
            }
        }

        this.parseSection(framework, compositionTypeSection, ParserState.COMPOSITION_TYPE);
        this.parseSection(framework, composableModuleSection, ParserState.COMPOSABLE_MODULE);
        this.parseSection(framework, compositionalStructureSection,
                ParserState.COMPOSITIONAL_STRUCTURE);
        this.parseSection(framework, propertySection, ParserState.PROPERTY);
        this.parseSection(framework, compositionRuleSection, ParserState.COMPOSITION_RULE);
        if (addDummies) {
            framework.addDummyAndAliasRulesIfNecessary();
        }
        return framework;
    }

    private void findTheoryPath(final String currentLine, final FrameworkRepresentation framework) {
        String line = currentLine;
        final String nameLineSeparator = " - ";
        if (line.contains(nameLineSeparator)) {
            final String[] splits = line.split(nameLineSeparator);
            line = splits[0];
            framework.setSessionName(splits[1]);
        }
        line = StringUtils.removeWhitespace(
                line.replace(ExtendedPrologStrings.THEORY_PATH_PREFIX, StringUtils.EMPTY)
                .replace(ExtendedPrologStrings.COMMENT, StringUtils.EMPTY));
        if (line.endsWith(IsabelleUtils.ROOT)) {
            line = line.substring(0, line.length() - IsabelleUtils.ROOT.length());
        }
        framework.setTheoryPath(line);
    }

    private List<ComponentType> extractParameters(final String component)
            throws MalformedEplFileException {
        final List<ComponentType> res = new LinkedList<ComponentType>();
        if (!component.contains(StringUtils.OPENING_PARENTHESIS)
                || component.endsWith(
                        StringUtils.OPENING_PARENTHESIS + StringUtils.CLOSING_PARENTHESIS)) {
            // No parameters.
            return res;
        }

        // Opening, but no closing bracket.
        if (!component.contains(StringUtils.CLOSING_PARENTHESIS)) {
            LOGGER.error("Opening, but no closing bracket on: \"" + component
                    + StringUtils.QUOTATION);
            throw new MalformedEplFileException();
        }

        final String regex = PARENTH_REGEX;
        final Pattern pattern = Pattern.compile(regex);
        final Matcher matcher = pattern.matcher(component);

        if (matcher.find()) {
            String parameterString = matcher.group();
            // Remove whitespace.
            parameterString = parameterString.replace(StringUtils.SPACE, StringUtils.EMPTY);
            // Get rid of parentheses.
            parameterString = parameterString.substring(1, parameterString.length() - 1);
            final String[] parameters = parameterString.split(StringUtils.COMMA);
            for (int i = 0; i < parameters.length; i++) {
                res.add(new ComponentType(parameters[i]));
            }
        } else {
            // This should never happen.
            throw new MalformedEplFileException();
        }
        return res;
    }

    private ParserState newState(final String line, final ParserState oldState) {
        ParserState toReturn = oldState;
        if (line.toUpperCase().contains(ExtendedPrologStrings.COMPOSITION_TYPE_HEADER)) {
            toReturn = ParserState.COMPOSITION_TYPE;
        } else if (line.toUpperCase().contains(ExtendedPrologStrings.COMPOSABLE_MODULE_HEADER)) {
            toReturn = ParserState.COMPOSABLE_MODULE;
        } else if (line.toUpperCase()
                .contains(ExtendedPrologStrings.COMPOSITIONAL_STRUCTURE_HEADER)) {
            toReturn = ParserState.COMPOSITIONAL_STRUCTURE;
        } else if (line.toUpperCase().contains(ExtendedPrologStrings.PROPERTY_HEADER)) {
            toReturn = ParserState.PROPERTY;
        } else if (line.toUpperCase().contains(ExtendedPrologStrings.COMPOSITION_RULE_HEADER)) {
            toReturn = ParserState.COMPOSITION_RULE;
        }
        return toReturn;
    }

    private void parseCompositionRuleSection(final FrameworkRepresentation framework,
                                             final List<String> lines)
                                                     throws MalformedEplFileException {
        String origin = StringUtils.EMPTY;
        String name = StringUtils.EMPTY;
        String prologString = StringUtils.EMPTY;
        // Starting at 1, because of header.
        for (int i = 1; i < lines.size(); i++) {
            final String currentLine = lines.get(i);
            if (origin.isEmpty()) {
                // No origin.
                if (!currentLine.startsWith(ExtendedPrologStrings.FORMATTER)) {
                    LOGGER.error("No origin specified for: \"" + currentLine
                            + StringUtils.QUOTATION);
                    throw new MalformedEplFileException();
                } else {
                    origin = this.sanitizeLine(currentLine);
                    continue;
                }
            } else {
                if (name.isEmpty()) {
                    // No name.
                    name = this.sanitizeLine(currentLine);
                    continue;
                } else {
                    // Origin and name set, looking for Prolog clause now.
                    prologString += currentLine;
                    if (currentLine.contains(StringUtils.PERIOD)) {
                        // Clause finished. Start Prolog Parser.
                        final PrologClause clause =
                                this.prologParser.parseSingleClause(prologString);
                        framework.add(new CompositionRule(name, origin, clause));
                        origin = StringUtils.EMPTY;
                        name = StringUtils.EMPTY;
                        prologString = StringUtils.EMPTY;
                    }
                }
            }
        }
    }

    private void parseCompositionTypeSection(final FrameworkRepresentation framework,
                                             final List<String> lines)
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
                    LOGGER.error("No type defined for \"" + currentLine + "\".");
                    throw new MalformedEplFileException();
                }
                currentLine = this.sanitizeLine(currentLine);
                final List<ComponentType> parameters = this.extractParameters(currentLine);
                currentLine = this.removeBracketExpression(currentLine);
                framework.add(new Component(currentType, currentLine, parameters));
            }
        }
    }

    private void parseSection(final FrameworkRepresentation framework, final List<String> lines,
                              final ParserState state) throws MalformedEplFileException {
        if (lines.isEmpty()) {
            return;
        }
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
        default: // skip operation, invalid call.
        }
    }

    private void parseSimpleSection(final FrameworkRepresentation framework,
                                    final List<String> lines, final ParserState state)
                                            throws MalformedEplFileException {
        final String header = lines.get(0);
        ComponentType type = null;

        // Modules that can be composed are the core component of the framework, the type's name
        // shall be changeable.
        if (state == ParserState.COMPOSABLE_MODULE) {
            final String[] splits = header.split("-");
            if (splits.length > 1) {
                if (splits.length == 2) {
                    // Alias is defined, this shall be a type.
                    final String typeString = this.sanitizeLine(splits[1]);
                    type = new ComponentType(typeString);
                    framework.setAlias(typeString);
                } else {
                    LOGGER.error("Malformed header: \"" + lines.get(0) + "\"");
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
            final List<ComponentType> parameters = this.extractParameters(name);
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
            default: // skip operation, invalid call.
            }
        }
    }

    private String removeBracketExpression(final String string) {
        final String regex = PARENTH_REGEX;
        final Pattern pattern = Pattern.compile(regex);
        final Matcher matcher = pattern.matcher(string);
        String copyOfString = string;
        if (matcher.find()) {
            final String parameterString = matcher.group();
            // Remove parameters from component for simpler processing in calling method.
            copyOfString = string.replace(parameterString, StringUtils.EMPTY);
        }
        return copyOfString;
    }

    private String sanitizeLine(final String line) {
        return StringUtils.removeWhitespace(line.replaceAll("=", StringUtils.EMPTY));
    }
}
