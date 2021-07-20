package com.fr2501.virage.isabelle;

import java.io.File;
import java.io.IOException;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import com.fr2501.util.Pair;
import com.fr2501.virage.core.ConfigReader;
import com.fr2501.virage.prolog.PrologParser;
import com.fr2501.virage.prolog.SimplePrologParser;
import com.fr2501.virage.types.Component;
import com.fr2501.virage.types.ComponentType;
import com.fr2501.virage.types.CompositionRule;
import com.fr2501.virage.types.ExternalSoftwareUnavailableException;
import com.fr2501.virage.types.FrameworkRepresentation;
import com.fr2501.virage.types.IsabelleBuildFailedException;
import com.fr2501.virage.types.Property;

/**
 * Extracts a {@link FrameworkRepresentation} from an Isabelle session.
 *
 */
public final class IsabelleFrameworkExtractor {
    private final Logger logger = LogManager.getRootLogger();

    private final PrologParser parser;
    private final List<String> prologStrings;

    /**
     * Simple constructor.
     */
    public IsabelleFrameworkExtractor() {
        this.parser = new SimplePrologParser();

        this.prologStrings = new LinkedList<String>();
    }

    private String buildPrologClauseString(final String succedent, final List<String> antecedents) {
        String res = succedent;

        if (!antecedents.isEmpty()) {
            res += " :- ";

            for (final String antecedent : antecedents) {
                res += antecedent + ", ";
            }

            res = res.substring(0, res.length() - 2);
        }

        res += ".";

        return res;
    }

    private void convertComponents(final FrameworkRepresentation framework,
            final Map<String, Map<String, String>> compsRaw) {
        for (final String thyName : compsRaw.keySet()) {
            final Map<String, String> currentThyContent = compsRaw.get(thyName);

            for (String compName : currentThyContent.keySet()) {
                final String typeString = currentThyContent.get(compName);
                compName = compName.replace(thyName.split("\\.")[1] + ".", "");

                final List<String> compType = this.parseType(typeString);

                final String compReturnTypeName = compType.get(compType.size() - 1);
                final ComponentType compReturnType = this.findOrAdd(framework, compReturnTypeName);
                final List<ComponentType> params = new LinkedList<ComponentType>();
                // size()-1, as the last member is the return type
                for (int i = 0; i < compType.size() - 1; i++) {
                    final String paramName = compType.get(i);
                    params.add(this.findOrAdd(framework, paramName));
                }

                if (compReturnTypeName.equals("(HOL.bool)")) {
                    final Property prop = new Property(compName, params);
                    framework.add(prop);
                } else {
                    /*
                     * if (params.contains(compReturnType)) { CompositionalStructure struct = new
                     * CompositionalStructure(compName, compReturnType, params);
                     * framework.add(struct); } else
                     */ {
                         final Component res = new Component(compReturnType, compName, params);
                         framework.add(res);
                     }
                }
            }
        }
    }

    private void convertCompositionRules(final FrameworkRepresentation framework,
            final Map<String, Map<String, String>> compRulesRaw) {
        for (final String thyName : compRulesRaw.keySet()) {
            thmLoop: for (final String thmName : compRulesRaw.get(thyName).keySet()) {
                String sign = compRulesRaw.get(thyName).get(thmName);
                sign = sign.replaceAll("[\n]+", " ");
                sign = sign.replaceAll("[\\s]+", " ");

                // Remove theory prefixes of constants
                sign = sign.replaceAll("\\?\\?\\.\\w+\\.", "");
                sign = sign.replaceAll("[A-Z]\\w+\\.", "");

                // Composition Rules are very limited on the operators they can contain.
                final Pattern allowedChars = Pattern.compile("[A-Za-z0-9,_\\(\\)\\.]+");

                final List<String> antecedents = new LinkedList<String>();
                String succedent = "";
                if (sign.contains("\\<Longrightarrow>")) {
                    final String[] splits = sign.split("\\\\<Longrightarrow>");

                    String antecedentString = splits[0];

                    antecedentString = antecedentString.replace("\\<lbrakk>", "")
                            .replace("\\<rbrakk>", "");

                    final String[] antecedentStringSplits = antecedentString.split(";");
                    for (final String ant : antecedentStringSplits) {
                        antecedents.add(this.convertIsabelleToProlog(this.replaceVariables(ant)));
                    }

                    succedent = this.convertIsabelleToProlog(this.replaceVariables(splits[1]));
                } else {
                    succedent = this.convertIsabelleToProlog(this.replaceVariables(sign));
                }

                Matcher matcher = allowedChars.matcher(succedent);
                if (!matcher.matches()) {
                    continue thmLoop;
                }

                for (final String ant : antecedents) {
                    matcher = allowedChars.matcher(ant);
                    if (!matcher.matches()) {
                        continue thmLoop;
                    }
                }

                final String prologString = this.buildPrologClauseString(succedent, antecedents);

                try {
                    final CompositionRule rule = new CompositionRule(thmName,
                            thyName.split("\\.")[1] + ".thy",
                            this.parser.parseSingleClause(prologString));

                    framework.add(rule);

                    this.prologStrings.add(prologString);
                } catch (final IllegalArgumentException e) {
                    this.logger.warn(e);
                }
            }
        }
    }

    private String convertIsabelleToProlog(final String s) {
        boolean insideBrackets = false;
        String res = "";

        final String copyOfs = s.strip();

        for (int i = 0; i < copyOfs.length(); i++) {
            final char cur = copyOfs.charAt(i);

            switch (cur) {
            case '(':
                if (insideBrackets) {
                    final int endIdx = this.findMatchingBracket(copyOfs, i);

                    if (endIdx == -1) {
                        // System.out.println("\t\t\tError");
                        continue;
                    }

                    res += this.convertIsabelleToProlog(copyOfs.substring(i + 1, endIdx));
                    if (endIdx < copyOfs.length() - 1 && copyOfs.charAt(endIdx + 1) != ')') {
                        res += ",";
                    }
                    i = endIdx + 1;
                } else {
                    insideBrackets = true;
                    res += cur;
                }
                break;
            case ' ':
                if (insideBrackets) {
                    res += ",";
                } else {
                    res += '(';
                    insideBrackets = true;
                }
                break;
            default:
                res += cur;
                break;
            }
        }

        res += ')';
        return res;
    }

    public FrameworkRepresentation extract(final String sessionDir, final String sessionName)
            throws ExternalSoftwareUnavailableException, IsabelleBuildFailedException {

        return this.extract(sessionDir, sessionName,
                "framework" + System.currentTimeMillis() + ".pl");
    }

    /**
     * Extracts a {@link FrameworkRepresentation} from an Isabelle session.
     *
     * @param sessionDir the directory of the session
     * @param sessionName the name of the session
     * @return a framework representation of the session
     * @throws ExternalSoftwareUnavailableException if Isabelle is unavailable
     * @throws IsabelleBuildFailedException if the session build fails
     */
    public FrameworkRepresentation extract(final String sessionDir, final String sessionName,
            final String fileName)
                    throws ExternalSoftwareUnavailableException, IsabelleBuildFailedException {
        if (fileName == null) {
            return this.extract(sessionDir, sessionName);
        }

        final ScalaIsabelleFacade facade = new ScalaIsabelleFacade(sessionDir, sessionName);

        final File plFile = new File(sessionDir + File.separator + fileName);
        try {
            plFile.createNewFile();
        } catch (final IOException e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
        }

        final FrameworkRepresentation framework = new FrameworkRepresentation(
                plFile.getAbsolutePath());

        framework.setAbsolutePath(plFile.getAbsolutePath());

        framework.setTheoryPath(sessionDir);
        framework.setSessionName(sessionName);

        final Map<String, Map<String, String>> compRulesRaw = facade.getTheorems();
        final Map<String, Map<String, String>> compsRaw = facade.getFunctionsAndDefinitions();

        this.convertComponents(framework, compsRaw);
        this.convertCompositionRules(framework, compRulesRaw);

        framework.addDummyRulesIfNecessary();

        return framework;
    }

    /**
     * Finds the position of the closing bracket for the one at idx.
     *
     * @param s the string
     * @param idx index of the opening bracket
     * @return index of the closing bracket
     */
    public int findMatchingBracket(final String s, final int idx) {
        int depth = 0;

        for (int i = idx; i < s.length(); i++) {
            final char cur = s.charAt(i);

            if (cur == '(') {
                depth++;
            }
            if (cur == ')') {
                depth--;
            }

            if (depth == 0) {
                return i;
            }
        }

        return -1;
    }

    private ComponentType findOrAdd(final FrameworkRepresentation framework, final String name) {
        String copyOfName = name;

        if (name.startsWith("(") && name.endsWith(")")) {
            copyOfName = name.substring(1, name.length() - 1);
        }

        for (final ComponentType frameworkType : framework.getComponentTypes()) {
            if (frameworkType.getName().equals(copyOfName)) {
                return frameworkType;
            }
        }

        final ComponentType res = new ComponentType(copyOfName);
        framework.add(res);
        return res;
    }

    private List<String> parseFun(final String funString) {
        String first = "";
        String second = "";

        int depth = 0;
        boolean readingFirst = false;

        // Omit "(fun" and trailing ")".
        for (int i = 4; i < funString.length() - 1; i++) {
            final char current = funString.charAt(i);

            if (current == '(') {
                depth++;
            }

            if (current == ')') {
                depth--;
            }

            if (depth == 1) {
                if (current == '(') {
                    readingFirst = !readingFirst;
                }
            }

            if (readingFirst) {
                first += current;
            } else {
                second += current;
            }
        }

        final List<String> firstList;
        final List<String> secondList;

        if (first.contains("fun")) {
            firstList = this.parseFun(first);
        } else {
            firstList = new LinkedList<String>();
            firstList.add(first);
        }

        if (second.contains("fun")) {
            secondList = this.parseFun(second);
        } else {
            secondList = new LinkedList<String>();
            secondList.add(second);
        }

        firstList.addAll(secondList);
        return firstList;
    }

    private List<String> parseType(final String passedTypeString) {
        String typeString = passedTypeString;

        List<String> res = new LinkedList<String>();

        final ConfigReader reader = ConfigReader.getInstance();
        final List<Pair<String, String>> replacements = reader.getTypeSynonyms();

        for (final Pair<String, String> synonym : replacements) {
            typeString = typeString.replace(synonym.getFirstValue(), synonym.getSecondValue());
        }

        if (typeString.startsWith("(fun")) {
            res = this.parseFun(typeString);
        } else {
            res.add(typeString);
        }

        return res;
    }

    private String replaceVariables(final String isaString) {
        String prologString = isaString;

        final Pattern pattern = Pattern.compile("\\?[a-z0-9]+");
        Matcher matcher = pattern.matcher(prologString);
        while (matcher.find()) {
            final String varName = prologString.substring(matcher.start(), matcher.end());
            prologString = prologString.replaceAll("\\" + varName, varName.toUpperCase());

            matcher = pattern.matcher(prologString);
        }

        prologString = prologString.replace("?", "");
        return prologString;
    }

}
