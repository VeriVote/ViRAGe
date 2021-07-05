package com.fr2501.virage.isabelle;

import com.fr2501.util.Pair;
import com.fr2501.virage.core.ConfigReader;
import com.fr2501.virage.prolog.PrologParser;
import com.fr2501.virage.prolog.SimplePrologParser;
import com.fr2501.virage.types.Component;
import com.fr2501.virage.types.ComponentType;
import com.fr2501.virage.types.CompositionRule;
import com.fr2501.virage.types.CompositionalStructure;
import com.fr2501.virage.types.ExternalSoftwareUnavailableException;
import com.fr2501.virage.types.FrameworkRepresentation;
import com.fr2501.virage.types.IsabelleBuildFailedException;
import com.fr2501.virage.types.Property;
import java.io.File;
import java.io.IOException;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

/**
 * Extracts a {@link FrameworkRepresentation} from an Isabelle session.
 *
 */
public class IsabelleFrameworkExtractor {
  private Logger logger = LogManager.getRootLogger();

  private PrologParser parser;
  private List<String> prologStrings;

  /**
   * Simple constructor.
   */
  public IsabelleFrameworkExtractor() {
    this.parser = new SimplePrologParser();

    this.prologStrings = new LinkedList<String>();
  }

  /**
   * Extracts a {@link FrameworkRepresentation} from an Isabelle session.

   * @param sessionDir the directory of the session
   * @param sessionName the name of the session
   * @return a framework representation of the session
   * @throws ExternalSoftwareUnavailableException if Isabelle is unavailable
   * @throws IsabelleBuildFailedException if the session build fails
   */
  public FrameworkRepresentation extract(String sessionDir, String sessionName)
      throws ExternalSoftwareUnavailableException, IsabelleBuildFailedException {
    ScalaIsabelleFacade facade = new ScalaIsabelleFacade(sessionDir, sessionName);

    File plFile;
    try {
      plFile = File.createTempFile("framework", ".pl");

      plFile.deleteOnExit();

      FrameworkRepresentation framework = new FrameworkRepresentation(plFile.getAbsolutePath());

      framework.setAbsolutePath(plFile.getAbsolutePath());

      framework.setTheoryPath(sessionDir);
      framework.setSessionName(sessionName);

      Map<String, Map<String, String>> compRulesRaw = facade.getTheorems();
      Map<String, Map<String, String>> compsRaw = facade.getFunctionsAndDefinitions();

      this.convertComponents(framework, compsRaw);
      this.convertCompositionRules(framework, compRulesRaw);

      framework.addDummyRulesIfNecessary();

      return framework;
    } catch (IOException e) {
      // TODO Auto-generated catch block
      e.printStackTrace();
    }

    return null;
  }

  private void convertComponents(FrameworkRepresentation framework,
      Map<String, Map<String, String>> compsRaw) {
    for (String thyName : compsRaw.keySet()) {
      Map<String, String> currentThyContent = compsRaw.get(thyName);

      for (String compName : currentThyContent.keySet()) {
        String typeString = currentThyContent.get(compName);
        compName = compName.replace(thyName.split("\\.")[1] + ".", "");

        List<String> compType = this.parseType(typeString);

        String compReturnTypeName = compType.get(compType.size() - 1);
        ComponentType compReturnType = this.findOrAdd(framework, compReturnTypeName);
        List<ComponentType> params = new LinkedList<ComponentType>();
        // size()-1, as the last member is the return type
        for (int i = 0; i < compType.size() - 1; i++) {
          String paramName = compType.get(i);
          params.add(this.findOrAdd(framework, paramName));
        }

        if (compReturnTypeName.equals("(HOL.bool)")) {
          Property prop = new Property(compName, params);
          framework.add(prop);
        } else {
          /* if (params.contains(compReturnType)) {
            CompositionalStructure struct = new CompositionalStructure(compName, compReturnType, params);
            framework.add(struct);
          } else */ {
            Component res = new Component(compReturnType, compName, params);
            framework.add(res);
          }
        }
      }
    }
  }

  private ComponentType findOrAdd(FrameworkRepresentation framework, String name) {
    if (name.startsWith("(") && name.endsWith(")")) {
      name = name.substring(1, name.length() - 1);
    }

    for (ComponentType frameworkType : framework.getComponentTypes()) {
      if (frameworkType.getName().equals(name)) {
        return frameworkType;
      }
    }

    ComponentType res = new ComponentType(name);
    framework.add(res);
    return res;
  }

  private List<String> parseType(String typeString) {
    List<String> res = new LinkedList<String>();

    ConfigReader reader = ConfigReader.getInstance();
    List<Pair<String, String>> replacements = reader.getTypeSynonyms();

    for (Pair<String, String> synonym : replacements) {
      typeString = typeString.replace(synonym.getFirstValue(), synonym.getSecondValue());
    }

    if (typeString.startsWith("(fun")) {
      res = this.parseFun(typeString);
    } else {
      res.add(typeString);
    }

    return res;
  }

  private List<String> parseFun(String funString) {
    String first = "";
    String second = "";

    int depth = 0;
    boolean readingFirst = false;

    // Omit "(fun" and trailing ")".
    for (int i = 4; i < funString.length() - 1; i++) {
      char current = funString.charAt(i);

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

    List<String> firstList;
    List<String> secondList;

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

  private void convertCompositionRules(FrameworkRepresentation framework,
      Map<String, Map<String, String>> compRulesRaw) {
    for (String thyName : compRulesRaw.keySet()) {
      thmLoop: for (String thmName : compRulesRaw.get(thyName).keySet()) {
        String sign = compRulesRaw.get(thyName).get(thmName);
        sign = sign.replaceAll("[\n]+", " ");
        sign = sign.replaceAll("[\\s]+", " ");

        // Remove theory prefixes of constants
        sign = sign.replaceAll("\\?\\?\\.\\w+\\.", "");

        // Composition Rules are very limited on the operators they can contain.
        Pattern allowedChars = Pattern.compile("[A-Za-z0-9,_\\(\\)]+");

        List<String> antecedents = new LinkedList<String>();
        String succedent = "";
        if (sign.contains("\\<Longrightarrow>")) {
          String[] splits = sign.split("\\\\<Longrightarrow>");

          String antecedentString = splits[0];

          antecedentString = antecedentString.replace("\\<lbrakk>", "").replace("\\<rbrakk>", "");

          String[] antecedentStringSplits = antecedentString.split(";");
          for (String ant : antecedentStringSplits) {
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

        for (String ant : antecedents) {
          matcher = allowedChars.matcher(ant);
          if (!matcher.matches()) {
            continue thmLoop;
          }
        }

        String prologString = this.buildPrologClauseString(succedent, antecedents);

        try {
          CompositionRule rule = new CompositionRule(thmName, thyName.split("\\.")[1] + ".thy",
              this.parser.parseSingleClause(prologString));

          framework.add(rule);

          this.prologStrings.add(prologString);
        } catch (IllegalArgumentException e) {
          logger.warn(e);
        }
      }
    }
  }

  private String buildPrologClauseString(String succedent, List<String> antecedents) {
    String res = succedent;

    if (!antecedents.isEmpty()) {
      res += " :- ";

      for (String antecedent : antecedents) {
        res += antecedent + ", ";
      }

      res = res.substring(0, res.length() - 2);
    }

    res += ".";

    return res;
  }

  private String replaceVariables(String isaString) {
    String prologString = isaString;

    Pattern pattern = Pattern.compile("\\?[a-z0-9]+");
    Matcher matcher = pattern.matcher(prologString);
    while (matcher.find()) {
      String varName = prologString.substring(matcher.start(), matcher.end());
      prologString = prologString.replaceAll("\\" + varName, varName.toUpperCase());

      matcher = pattern.matcher(prologString);
    }

    prologString = prologString.replace("?", "");
    return prologString;
  }

  private String convertIsabelleToProlog(String s) {
    boolean insideBrackets = false;
    String res = "";

    s = s.strip();

    for (int i = 0; i < s.length(); i++) {
      char cur = s.charAt(i);

      switch (cur) {
        case '(':
          if (insideBrackets) {
            int endIdx = this.findMatchingBracket(s, i);
  
            if (endIdx == -1) {
              // System.out.println("\t\t\tError");
              continue;
            }
  
            res += this.convertIsabelleToProlog(s.substring(i + 1, endIdx));
            if (endIdx < s.length() - 1 && s.charAt(endIdx + 1) != ')') {
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

  /**
   * Finds the position of the closing bracket for the one at idx.

   * @param s the string
   * @param idx index of the opening bracket
   * @return index of the closing bracket
   */
  public int findMatchingBracket(String s, int idx) {
    int depth = 0;

    for (int i = idx; i < s.length(); i++) {
      char cur = s.charAt(i);

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

}
