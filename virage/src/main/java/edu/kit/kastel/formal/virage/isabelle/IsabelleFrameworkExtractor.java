package edu.kit.kastel.formal.virage.isabelle;

import java.io.File;
import java.io.IOException;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import edu.kit.kastel.formal.util.Pair;
import edu.kit.kastel.formal.util.StringUtils;
import edu.kit.kastel.formal.util.SystemUtils;
import edu.kit.kastel.formal.virage.core.ConfigReader;
import edu.kit.kastel.formal.virage.prolog.JplFacade;
import edu.kit.kastel.formal.virage.prolog.PrologParser;
import edu.kit.kastel.formal.virage.prolog.PrologPredicate;
import edu.kit.kastel.formal.virage.prolog.SimplePrologParser;
import edu.kit.kastel.formal.virage.types.Component;
import edu.kit.kastel.formal.virage.types.ComponentType;
import edu.kit.kastel.formal.virage.types.CompositionRule;
import edu.kit.kastel.formal.virage.types.ExternalSoftwareUnavailableException;
import edu.kit.kastel.formal.virage.types.FrameworkExtractionFailedException;
import edu.kit.kastel.formal.virage.types.FrameworkRepresentation;
import edu.kit.kastel.formal.virage.types.IsabelleBuildFailedException;
import edu.kit.kastel.formal.virage.types.Property;

/**
 * Extracts a {@link FrameworkRepresentation} from an Isabelle session.
 *
 * @author VeriVote
 */
public final class IsabelleFrameworkExtractor {
    /**
     * Regular expression for dots.
     */
    private static final String DOT_REGEX = "\\.";

    /**
     * Regular expression for question marks.
     */
    private static final String QST_REGEX = "\\?";

    /**
     * The logger.
     */
    private final Logger logger = LogManager.getRootLogger();

    /**
     * The Prolog parser.
     */
    private final PrologParser parser;

    /**
     * List of Prolog Strings.
     */
    private final List<String> prologStrings;

    /**
     * Simple constructor.
     */
    public IsabelleFrameworkExtractor() {
        this.parser = new SimplePrologParser();
        this.prologStrings = new LinkedList<String>();
    }

    private static String buildPrologClauseString(final String succedent,
                                                  final List<String> antecedents) {
        final StringBuilder res = new StringBuilder(succedent);
        if (!antecedents.isEmpty()) {
            res.append(StringUtils.SPACE + PrologParser.NECK + StringUtils.SPACE);
            for (final String antecedent: antecedents) {
                res.append(antecedent + StringUtils.COMMA + StringUtils.SPACE);
            }
            res.delete(res.length() - 2, res.length() - 1);
        }
        res.append(StringUtils.PERIOD);
        return res.toString();
    }

    private static void convertComponents(final FrameworkRepresentation framework,
                                          final Map<String, Map<String, String>> compsRaw) {
        for (final Map.Entry<String, Map<String, String>> thy: compsRaw.entrySet()) {
            final Map<String, String> currentThyContent = thy.getValue();
            for (final Map.Entry<String, String> componentIterated: currentThyContent.entrySet()) {
                String compName = componentIterated.getKey();
                final String typeString = componentIterated.getValue();
                compName = compName.replace(thy.getKey().split(DOT_REGEX)[1] + StringUtils.PERIOD,
                                            StringUtils.EMPTY);
                final List<String> compType = parseType(typeString);
                final String compReturnTypeName = compType.get(compType.size() - 1);
                final ComponentType compReturnType = findOrAdd(framework, compReturnTypeName);
                final List<ComponentType> parameters = new LinkedList<ComponentType>();
                // size()-1, as the last member is the return type
                for (int i = 0; i < compType.size() - 1; i++) {
                    final String paramName = compType.get(i);
                    parameters.add(findOrAdd(framework, paramName));
                }
                if ((StringUtils.parenthesize(IsabelleUtils.BOOL)).equals(compReturnTypeName)) {
                    final Property prop = new Property(compName, parameters);
                    framework.add(prop);
                } else {
                    /*
                     * if (params.contains(compReturnType)) {
                     *   CompositionalStructure structure =
                     *     new CompositionalStructure(compName, compReturnType, parameters);
                     *     framework.add(structure);
                     * } else
                     */
                    final Component res = new Component(compReturnType, compName, parameters);
                    framework.add(res);
                }
            }
        }
    }

    private void convertCompositionRules(final FrameworkRepresentation framework,
                                         final Map<String, Map<String, String>> compRulesRaw) {
        for (final Map.Entry<String, Map<String, String>> thy: compRulesRaw.entrySet()) {
            thmLoop: for (final Map.Entry<String, String> thm: thy.getValue().entrySet()) {
                String sign = thm.getValue();
                sign = sign.replaceAll("[\n]+", StringUtils.SPACE);
                sign = sign.replaceAll("[\\s]+", StringUtils.SPACE);

                // Remove theory prefixes of constants
                sign = sign.replaceAll(QST_REGEX + QST_REGEX + DOT_REGEX + "\\w+" + DOT_REGEX,
                                       StringUtils.EMPTY);
                sign = sign.replaceAll("[A-Z]\\w+" +  DOT_REGEX, StringUtils.EMPTY);
                // Composition Rules are very limited on the operators they can contain.
                final Pattern allowedChars =
                        Pattern.compile("[A-Za-z0-9,_\\(\\)" + DOT_REGEX + "]+");

                final List<String> antecedents = new LinkedList<String>();
                String succedent = StringUtils.EMPTY;
                if (sign.contains("\\<Longrightarrow>")) {
                    final String[] splits = sign.split("\\\\<Longrightarrow>");
                    String antecedentString = splits[0];
                    antecedentString =
                            antecedentString
                            .replace("\\<lbrakk>", StringUtils.EMPTY)
                            .replace("\\<rbrakk>", StringUtils.EMPTY);
                    final String[] antecedentStringSplits = antecedentString.split(";");
                    for (final String ant: antecedentStringSplits) {
                        antecedents.add(convertIsabelleToProlog(replaceVariables(ant)));
                    }
                    succedent = convertIsabelleToProlog(replaceVariables(splits[1]));
                } else {
                    succedent = convertIsabelleToProlog(replaceVariables(sign));
                }

                Matcher matcher = allowedChars.matcher(succedent);
                if (!matcher.matches()) {
                    continue thmLoop;
                }
                for (final String ant: antecedents) {
                    matcher = allowedChars.matcher(ant);
                    if (!matcher.matches()) {
                        continue thmLoop;
                    }
                }
                final List<String> prologStringList = new LinkedList<String>();
                prologStringList.add(buildPrologClauseString(succedent, antecedents));
                try {
                    for (final String prologString: prologStringList) {
                        final CompositionRule rule =
                                new CompositionRule(thm.getKey(),
                                                    thy.getKey().split(DOT_REGEX)[1]
                                                            + IsabelleUtils.DOT_THY,
                                                    this.parser.parseSingleClause(prologString));
                        framework.add(rule);
                        this.prologStrings.add(prologString);
                    }
                } catch (final IllegalArgumentException e) {
                    this.logger.warn(e);
                }
            }
        }
    }

    private static String convertIsabelleToProlog(final String s) {
        boolean insideBrackets = false;
        String res = StringUtils.EMPTY;
        final String copyOfs = s.strip();
        for (int i = 0; i < copyOfs.length();) {
            final char cur = copyOfs.charAt(i);
            switch (cur) {
            case StringUtils.LEFT_PAREN:
                if (insideBrackets) {
                    final int endIdx = findMatchingBracket(copyOfs, i);
                    if (endIdx == -1) {
                        // System.out.println("\t\t\tError");
                        continue;
                    }
                    res += convertIsabelleToProlog(copyOfs.substring(i + 1, endIdx));
                    if (endIdx < copyOfs.length() - 1
                            && copyOfs.charAt(endIdx + 1) != StringUtils.RIGHT_PAREN) {
                        res += StringUtils.COMMA;
                    }
                    i = endIdx + 1;
                } else {
                    insideBrackets = true;
                    res += cur;
                    i++;
                }
                break;
            case StringUtils.SPACE_CHAR:
                if (insideBrackets) {
                    res += StringUtils.COMMA;
                } else {
                    res += StringUtils.LEFT_PAREN;
                    insideBrackets = true;
                }
                i++;
                break;
            default:
                res += cur;
                i++;
                break;
            }
        }
        res += StringUtils.RIGHT_PAREN;
        return res;
    }

    /**
     * Extracts an (E)PL file from an Isabelle session.
     *
     * @param sessionDir the session directory
     * @param sessionName the session name
     * @return the compositional framework
     * @throws FrameworkExtractionFailedException wrapping the actual cause
     */
    public FrameworkRepresentation extract(final String sessionDir, final String sessionName)
            throws FrameworkExtractionFailedException {
        return extract(sessionDir, sessionName,
                       "framework" + System.currentTimeMillis() + PrologParser.DOT_PL);
    }

    /**
     * Extracts a {@link FrameworkRepresentation} from an Isabelle session.
     *
     * @param sessionDir the directory of the session
     * @param sessionName the name of the session
     * @param fileName the name of the new (E)PL file
     * @return a framework representation of the session
     * @throws FrameworkExtractionFailedException wrapping the actual cause
     */
    public FrameworkRepresentation extract(final String sessionDir, final String sessionName,
                                           final String fileName)
                                                   throws FrameworkExtractionFailedException {
        if (fileName == null) {
            return extract(sessionDir, sessionName);
        }
        final ScalaIsabelleFacade facade;
        try {
            facade = new ScalaIsabelleFacade(sessionDir, sessionName);
        } catch (ExternalSoftwareUnavailableException | IsabelleBuildFailedException e1) {
            throw new FrameworkExtractionFailedException(e1);
        }
        final File plFile = SystemUtils.file(sessionDir + File.separator + fileName);
        try {
            plFile.createNewFile();
        } catch (final IOException e) {
            e.printStackTrace();
        }
        final FrameworkRepresentation framework =
                new FrameworkRepresentation(plFile.getAbsolutePath());
        framework.setAbsolutePath(plFile.getAbsolutePath());
        framework.setTheoryPath(sessionDir);
        framework.setSessionName(sessionName);
        final Map<String, Map<String, String>> compRulesRaw = facade.getTheorems();
        final Map<String, Map<String, String>> compsRaw = facade.getFunctionsAndDefinitions();
        convertComponents(framework, compsRaw);
        this.convertCompositionRules(framework, compRulesRaw);
        framework.addDummyAndAliasRulesIfNecessary();
        return framework;
    }

    private Map<PrologPredicate, List<PrologPredicate>>
                computeTransitiveClosureOfComponentAliases() {
        final Map<String, String> input = ConfigReader.getInstance().getComponentAliases();
        final Map<PrologPredicate, List<PrologPredicate>> res =
                    new HashMap<PrologPredicate, List<PrologPredicate>>();
        for (final Map.Entry<String, String> in: input.entrySet()) {
            res.put(this.parser.parsePredicate(in.getKey()),
                    List.of(this.parser.parsePredicate(in.getValue())));
        }
        return res;

        // TODO Fix bug and actually compute transitive closure!
        /*
        final Map<PrologPredicate, List<PrologPredicate>> toReturn =
            new HashMap<PrologPredicate, List<PrologPredicate>>();
        for (final String predString: input.keySet()) {
            try {
                final List<PrologPredicate> toBePassed = new LinkedList<PrologPredicate>();
                toBePassed.add(this.parser.parsePredicate(input.get(predString)));
                toReturn.put(this.parser.parsePredicate(predString), toBePassed);
            } catch (final IllegalArgumentException e) {
                System.out.println(predString);
                throw new MalformedSettingsValueException(predString);
            }
        }
        boolean changesMade = true;
        while (changesMade) {
            changesMade = false;
            for (final PrologPredicate alias: toReturn.keySet()) {
                final List<PrologPredicate> aliasExpansions = toReturn.get(alias);
                for (final PrologPredicate candidate: toReturn.keySet()) {
                    if (candidate == alias) {
                        continue;
                    }
                    final List<PrologPredicate> candidateExpansions = toReturn.get(candidate);
                    final List<PrologPredicate> newValues =
                        computeAllExpansions(alias, aliasExpansions, candidateExpansions);
                    for (final PrologPredicate newValue: newValues) {
                        if (!candidateExpansions.contains(newValue)) {
                            candidateExpansions.add(newValue);
                            changesMade = true;
                        }
                    }
                }
            }
        }
        return toReturn; */
    }

    private static List<PrologPredicate>
                computeAllExpansions(final PrologPredicate alias,
                                     final List<PrologPredicate> aliasExpansions,
                                     final List<PrologPredicate> candidateExpansions)
                    throws ExternalSoftwareUnavailableException {
        final List<PrologPredicate> toReturn = new LinkedList<PrologPredicate>();
        for (final PrologPredicate candidateExpansion: candidateExpansions) {
            final List<PrologPredicate> children = candidateExpansion.getAllChildren();
            for (final PrologPredicate child: children) {
                if (child.getName().equals(alias.getName())) {
                    for (final PrologPredicate aliasExpansion: aliasExpansions) {
                        toReturn.add(replaceAlias(candidateExpansion, child, aliasExpansion));
                    }
                }
            }
        }
        return toReturn;
    }

    private static PrologPredicate replaceAlias(final PrologPredicate original,
                                                final PrologPredicate toBeReplaced,
                                                final PrologPredicate replacement)
                                                    throws ExternalSoftwareUnavailableException {
        final JplFacade facade = new JplFacade();
        boolean unifiable = true;
        Map<String, String> replacements = new HashMap<String, String>();
        try {
            replacements = facade.unifiable(toBeReplaced.toString(), original.toString());
        } catch (final IllegalArgumentException e) {
            unifiable = false;
        }
        if (replacements.keySet().contains(PrologPredicate.ANONYMOUS)) {
            replacements.remove(PrologPredicate.ANONYMOUS);
        }
        final boolean onlyOneVariable =
                original.isVariable() && !toBeReplaced.isVariable()
                || !original.isVariable() && toBeReplaced.isVariable();

        if (unifiable && !onlyOneVariable) {
            final PrologPredicate copyOfReplacement = PrologPredicate.copy(replacement);
            copyOfReplacement.replaceVariables(replacements);
            replacements.clear();
            final List<PrologPredicate> originalParameters =
                    PrologPredicate.copy(toBeReplaced).getParameters();
            final int oldIdx = 0;
            for (final PrologPredicate pred: copyOfReplacement.getAllChildren()) {
                if (pred.isVariable()) {
                    replacements.put(pred.getName(), originalParameters.get(oldIdx).toString());
                }
            }
            copyOfReplacement.replaceVariables(replacements);
            return copyOfReplacement;
        } else {
            final PrologPredicate copyOfOriginal = PrologPredicate.copy(original);
            for (int i = 0; i < copyOfOriginal.getArity(); i++) {
                copyOfOriginal.getParameters().set(i, replaceAlias(
                        copyOfOriginal.getParameters().get(i), toBeReplaced, replacement));
            }
            return copyOfOriginal;
        }
    }

    /**
     * Finds the position of the closing bracket for the one at the given index position.
     *
     * @param s the string
     * @param idx index position of the opening bracket
     * @return index of the closing bracket
     */
    private static int findMatchingBracket(final String s, final int idx) {
        int depth = 0;
        for (int i = idx; i < s.length(); i++) {
            final char cur = s.charAt(i);
            if (cur == StringUtils.LEFT_PAREN) {
                depth++;
            }
            if (cur == StringUtils.RIGHT_PAREN) {
                depth--;
            }
            if (depth == 0) {
                return i;
            }
        }
        return -1;
    }

    private static ComponentType findOrAdd(final FrameworkRepresentation framework,
                                           final String name) {
        String copyOfName = name;
        if (name.startsWith(StringUtils.OPENING_PARENTHESIS)
                && name.endsWith(StringUtils.CLOSING_PARENTHESIS)) {
            copyOfName = name.substring(1, name.length() - 1);
        }
        for (final ComponentType frameworkType: framework.getComponentTypes()) {
            if (frameworkType.getName().equals(copyOfName)) {
                return frameworkType;
            }
        }
        final ComponentType res = new ComponentType(copyOfName);
        framework.add(res);
        return res;
    }

    private static List<String> parseFun(final String funString) {
        final StringBuilder first = new StringBuilder(StringUtils.EMPTY);
        final StringBuilder second = new StringBuilder(StringUtils.EMPTY);
        int depth = 0;
        boolean readingFirst = false;
        // Omit "(fun" and trailing ")".
        for (int i = (IsabelleUtils.FUN + StringUtils.SPACE).length(); i < funString.length() - 1;
                i++) {
            final char current = funString.charAt(i);
            if (current == StringUtils.OPENING_PARENTHESIS.charAt(0)) {
                depth++;
            }
            if (current == StringUtils.CLOSING_PARENTHESIS.charAt(0)) {
                depth--;
            }
            if (depth == 1) {
                if (current == StringUtils.OPENING_PARENTHESIS.charAt(0)) {
                    readingFirst = !readingFirst;
                }
            }
            if (readingFirst) {
                first.append(current);
            } else {
                second.append(current);
            }
        }
        final List<String> firstList;
        final List<String> secondList;

        if (first.toString().contains(IsabelleUtils.FUN)) {
            firstList = parseFun(first.toString());
        } else {
            firstList = new LinkedList<String>();
            firstList.add(first.toString());
        }
        if (second.toString().contains(IsabelleUtils.FUN)) {
            secondList = parseFun(second.toString());
        } else {
            secondList = new LinkedList<String>();
            secondList.add(second.toString());
        }
        firstList.addAll(secondList);
        return firstList;
    }

    private static List<String> parseType(final String passedTypeString) {
        String typeString = passedTypeString;
        List<String> res = new LinkedList<String>();
        final ConfigReader reader = ConfigReader.getInstance();
        final List<Pair<String, String>> replacements = reader.getTypeSynonyms();
        for (final Pair<String, String> synonym: replacements) {
            typeString = typeString.replace(synonym.getFirstValue(), synonym.getSecondValue());
        }
        if (typeString.startsWith(StringUtils.OPENING_PARENTHESIS + IsabelleUtils.FUN)) {
            res = parseFun(typeString);
        } else {
            res.add(typeString);
        }
        return res;
    }

    private static String replaceVariables(final String isaString) {
        String prologString = isaString;
        final Pattern pattern = Pattern.compile(QST_REGEX + "[a-z0-9]+");
        Matcher matcher = pattern.matcher(prologString);
        while (matcher.find()) {
            final String varName = prologString.substring(matcher.start(), matcher.end());
            prologString = prologString.replaceAll("\\" + varName, varName.toUpperCase());
            matcher = pattern.matcher(prologString);
        }
        prologString = prologString.replace("?", StringUtils.EMPTY);
        return prologString;
    }
}
