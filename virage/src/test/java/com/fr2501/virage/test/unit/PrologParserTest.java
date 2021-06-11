package com.fr2501.virage.test.unit;

import static org.junit.Assert.assertTrue;

import com.fr2501.virage.prolog.PrologClause;
import com.fr2501.virage.prolog.PrologParser;
import com.fr2501.virage.prolog.PrologPredicate;
import com.fr2501.virage.prolog.SimplePrologParser;
import java.util.LinkedList;
import java.util.List;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import org.junit.Test;

public class PrologParserTest {
  private static final Logger logger = LogManager.getLogger(PrologParserTest.class);

  @Test(expected = IllegalArgumentException.class)
  public void parseEmptyClause() {
    logger.info("parseEmptyClause()");
    String clause = "";
    PrologParser parser = new SimplePrologParser();

    parser.parseSingleClause(clause);
  }

  @Test
  public void testEquals() {
    logger.info("testEquals()");
      {
        PrologClause clause1 = new PrologClause(new PrologPredicate("a"));
        assertTrue(clause1.equals(clause1));
      }

      {
        LinkedList<PrologPredicate> antecedents = new LinkedList<PrologPredicate>();
        antecedents.add(new PrologPredicate("b"));
        antecedents.add(new PrologPredicate("c"));
        PrologClause clause2 = new PrologClause(new PrologPredicate("a"), antecedents);
        assertTrue(clause2.equals(clause2));
      }

      {
        List<PrologPredicate> x = new LinkedList<PrologPredicate>();
        x.add(new PrologPredicate("X"));
        List<PrologPredicate> xy = new LinkedList<PrologPredicate>();
        xy.add(new PrologPredicate("X"));
        xy.add(new PrologPredicate("Y"));
  
        PrologPredicate a = new PrologPredicate("a", xy);
        PrologPredicate b = new PrologPredicate("b");
        PrologPredicate c = new PrologPredicate("c", x);
        PrologPredicate d = new PrologPredicate("d", xy);
  
        List<PrologPredicate> antecedents = new LinkedList<PrologPredicate>();
        antecedents.add(b);
        antecedents.add(c);
        antecedents.add(d);
  
        PrologClause clause3 = new PrologClause(a, antecedents);
        assertTrue(clause3.equals(clause3));
      }

      {
        List<PrologPredicate> x = new LinkedList<PrologPredicate>();
        x.add(new PrologPredicate("X"));
        List<PrologPredicate> y = new LinkedList<PrologPredicate>();
        x.add(new PrologPredicate("Y"));
        List<PrologPredicate> xy = new LinkedList<PrologPredicate>();
        xy.add(new PrologPredicate("X"));
        xy.add(new PrologPredicate("Y"));
        List<PrologPredicate> x1 = new LinkedList<PrologPredicate>();
        x1.add(new PrologPredicate("X"));
        x1.add(new PrologPredicate("1"));
  
        PrologPredicate seq = new PrologPredicate("sequential_composition", xy);
        PrologPredicate dli = new PrologPredicate("defer_lift_invariant", x);
        PrologPredicate nel = new PrologPredicate("non_electing", x);
        PrologPredicate ele = new PrologPredicate("electing", y);
        PrologPredicate def = new PrologPredicate("defers", x1);
  
        List<PrologPredicate> param = new LinkedList<PrologPredicate>();
        param.add(seq);
  
        PrologPredicate mono = new PrologPredicate("monotone", param);
  
        List<PrologPredicate> antecedents = new LinkedList<PrologPredicate>();
        antecedents.add(dli);
        antecedents.add(nel);
        antecedents.add(ele);
        antecedents.add(def);
  
        PrologClause clause4 = new PrologClause(mono, antecedents);
        assertTrue(clause4.equals(clause4));
      }
  }

  @Test
  public void parseFact() {
    logger.info("parseFact()");
    String clause = "a.";
    PrologClause res = new PrologClause(new PrologPredicate("a"));

    PrologParser parser = new SimplePrologParser();

    PrologClause parsed = parser.parseSingleClause(clause);

    assertTrue(parsed.equals(res));
  }

  @Test
  public void parseSimpleClause() {
    logger.info("parseSimpleClause()");
    String clause = "a :- b,c.";
    List<PrologPredicate> antecedents = new LinkedList<PrologPredicate>();
    antecedents.add(new PrologPredicate("b"));
    antecedents.add(new PrologPredicate("c"));
    PrologClause res = new PrologClause(new PrologPredicate("a"), antecedents);

    PrologParser parser = new SimplePrologParser();

    PrologClause parsed = parser.parseSingleClause(clause);

    assertTrue(parsed.equals(res));
  }

  @Test
  public void parseComplexClause() {
    logger.info("parseComplexClause()");
    String clause = "a(X,Y) :- b,c(X),d(X,Y).";

    List<PrologPredicate> x = new LinkedList<PrologPredicate>();
    x.add(new PrologPredicate("X"));
    List<PrologPredicate> xy = new LinkedList<PrologPredicate>();
    xy.add(new PrologPredicate("X"));
    xy.add(new PrologPredicate("Y"));

    PrologPredicate a = new PrologPredicate("a", xy);
    PrologPredicate b = new PrologPredicate("b");
    PrologPredicate c = new PrologPredicate("c", x);
    PrologPredicate d = new PrologPredicate("d", xy);

    List<PrologPredicate> antecedents = new LinkedList<PrologPredicate>();
    antecedents.add(b);
    antecedents.add(c);
    antecedents.add(d);

    PrologClause res = new PrologClause(a, antecedents);

    PrologParser parser = new SimplePrologParser();

    PrologClause parse = parser.parseSingleClause(clause);

    assertTrue(parse.equals(res));
  }

  @Test
  public void parseRealClause() {
    logger.info("parseRealClause()");
    String clause = "monotone(sequential_composition(X,Y)) "
        + ":- defer_lift_invariant(X),non_electing(X),defers(X,1),electing(Y).";

    List<PrologPredicate> x = new LinkedList<PrologPredicate>();
    x.add(new PrologPredicate("X"));
    List<PrologPredicate> y = new LinkedList<PrologPredicate>();
    y.add(new PrologPredicate("Y"));
    List<PrologPredicate> xy = new LinkedList<PrologPredicate>();
    xy.add(new PrologPredicate("X"));
    xy.add(new PrologPredicate("Y"));
    List<PrologPredicate> x1 = new LinkedList<PrologPredicate>();
    x1.add(new PrologPredicate("X"));
    x1.add(new PrologPredicate("1"));

    PrologPredicate seq = new PrologPredicate("sequential_composition", xy);
    PrologPredicate dli = new PrologPredicate("defer_lift_invariant", x);
    PrologPredicate nel = new PrologPredicate("non_electing", x);
    PrologPredicate def = new PrologPredicate("defers", x1);
    PrologPredicate ele = new PrologPredicate("electing", y);

    List<PrologPredicate> param = new LinkedList<PrologPredicate>();
    param.add(seq);

    PrologPredicate mono = new PrologPredicate("monotone", param);

    LinkedList<PrologPredicate> antecedents = new LinkedList<PrologPredicate>();
    antecedents.add(dli);
    antecedents.add(nel);
    antecedents.add(def);
    antecedents.add(ele);

    PrologClause reference = new PrologClause(mono, antecedents);

    PrologParser parser = new SimplePrologParser();
    PrologClause res = parser.parseSingleClause(clause);

    assertTrue(res.equals(reference));
  }
}
