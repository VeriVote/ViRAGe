package com.fr2501.virage.test.unit;

import static org.junit.Assert.assertTrue;

import java.util.LinkedList;
import java.util.List;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import org.junit.Test;

import com.fr2501.virage.prolog.PrologClause;
import com.fr2501.virage.prolog.PrologParser;
import com.fr2501.virage.prolog.PrologPredicate;
import com.fr2501.virage.prolog.SimplePrologParser;

/**
 * Test suite for {@link PrologParser}.
 *
 * @author VeriVote
 */
public class PrologParserTest {
    /**
     * The logger.
     */
    private static final Logger LOGGER = LogManager.getLogger(PrologParserTest.class);

    /**
     * Tests behavior on empty clause.
     */
    @Test(expected = IllegalArgumentException.class)
    public void parseEmptyClause() {
        LOGGER.info("parseEmptyClause()");
        final String clause = "";
        final PrologParser parser = new SimplePrologParser();

        parser.parseSingleClause(clause);
    }

    /**
     * Tests equality of parsed clauses.
     */
    @Test
    public void testEquals() {
        LOGGER.info("testEquals()");

        final PrologClause clause1 = new PrologClause(new PrologPredicate("a"));
        assertTrue(clause1.equals(clause1));

        final LinkedList<PrologPredicate> antecedents1 = new LinkedList<PrologPredicate>();
        antecedents1.add(new PrologPredicate("b"));
        antecedents1.add(new PrologPredicate("c"));
        final PrologClause clause2 = new PrologClause(new PrologPredicate("a"), antecedents1);
        assertTrue(clause2.equals(clause2));

        final List<PrologPredicate> x = new LinkedList<PrologPredicate>();
        x.add(new PrologPredicate("X"));
        final List<PrologPredicate> xy = new LinkedList<PrologPredicate>();
        xy.add(new PrologPredicate("X"));
        xy.add(new PrologPredicate("Y"));

        final PrologPredicate a = new PrologPredicate("a", xy);
        final PrologPredicate b = new PrologPredicate("b");
        final PrologPredicate c = new PrologPredicate("c", x);
        final PrologPredicate d = new PrologPredicate("d", xy);

        final List<PrologPredicate> antecedents2 = new LinkedList<PrologPredicate>();
        antecedents2.add(b);
        antecedents2.add(c);
        antecedents2.add(d);

        final PrologClause clause3 = new PrologClause(a, antecedents2);
        assertTrue(clause3.equals(clause3));

        final List<PrologPredicate> x2 = new LinkedList<PrologPredicate>();
        x2.add(new PrologPredicate("X"));
        final List<PrologPredicate> y = new LinkedList<PrologPredicate>();
        x2.add(new PrologPredicate("Y"));
        final List<PrologPredicate> xy2 = new LinkedList<PrologPredicate>();
        xy2.add(new PrologPredicate("X"));
        xy2.add(new PrologPredicate("Y"));
        final List<PrologPredicate> x1 = new LinkedList<PrologPredicate>();
        x1.add(new PrologPredicate("X"));
        x1.add(new PrologPredicate("1"));

        final PrologPredicate seq = new PrologPredicate("sequential_composition", xy2);
        final PrologPredicate dli = new PrologPredicate("defer_lift_invariant", x2);
        final PrologPredicate nel = new PrologPredicate("non_electing", x2);
        final PrologPredicate ele = new PrologPredicate("electing", y);
        final PrologPredicate def = new PrologPredicate("defers", x1);

        final List<PrologPredicate> param = new LinkedList<PrologPredicate>();
        param.add(seq);

        final PrologPredicate mono = new PrologPredicate("monotone", param);

        final List<PrologPredicate> antecedents = new LinkedList<PrologPredicate>();
        antecedents.add(dli);
        antecedents.add(nel);
        antecedents.add(ele);
        antecedents.add(def);

        final PrologClause clause4 = new PrologClause(mono, antecedents);
        assertTrue(clause4.equals(clause4));
    }

    /**
     * Tests parser on a fact.
     */
    @Test
    public void parseFact() {
        LOGGER.info("parseFact()");
        final String clause = "a.";
        final PrologClause res = new PrologClause(new PrologPredicate("a"));

        final PrologParser parser = new SimplePrologParser();

        final PrologClause parsed = parser.parseSingleClause(clause);

        assertTrue(parsed.equals(res));
    }

    /**
     * Tests parser on a simple clause.
     */
    @Test
    public void parseSimpleClause() {
        LOGGER.info("parseSimpleClause()");
        final String clause = "a :- b,c.";
        final List<PrologPredicate> antecedents = new LinkedList<PrologPredicate>();
        antecedents.add(new PrologPredicate("b"));
        antecedents.add(new PrologPredicate("c"));
        final PrologClause res = new PrologClause(new PrologPredicate("a"), antecedents);

        final PrologParser parser = new SimplePrologParser();

        final PrologClause parsed = parser.parseSingleClause(clause);

        assertTrue(parsed.equals(res));
    }

    /**
     * Tests parser on a complex clause.
     */
    @Test
    public void parseComplexClause() {
        LOGGER.info("parseComplexClause()");
        final String clause = "a(X,Y) :- b,c(X),d(X,Y).";

        final List<PrologPredicate> x = new LinkedList<PrologPredicate>();
        x.add(new PrologPredicate("X"));
        final List<PrologPredicate> xy = new LinkedList<PrologPredicate>();
        xy.add(new PrologPredicate("X"));
        xy.add(new PrologPredicate("Y"));

        final PrologPredicate a = new PrologPredicate("a", xy);
        final PrologPredicate b = new PrologPredicate("b");
        final PrologPredicate c = new PrologPredicate("c", x);
        final PrologPredicate d = new PrologPredicate("d", xy);

        final List<PrologPredicate> antecedents = new LinkedList<PrologPredicate>();
        antecedents.add(b);
        antecedents.add(c);
        antecedents.add(d);

        final PrologClause res = new PrologClause(a, antecedents);

        final PrologParser parser = new SimplePrologParser();

        final PrologClause parse = parser.parseSingleClause(clause);

        assertTrue(parse.equals(res));
    }

    /**
     * Tests parser on a clause from the Voting Rule Framework.
     */
    @Test
    public void parseRealClause() {
        LOGGER.info("parseRealClause()");
        final String clause = "monotone(sequential_composition(X,Y)) "
                + ":- defer_lift_invariant(X),non_electing(X),defers(X,1),electing(Y).";

        final List<PrologPredicate> x = new LinkedList<PrologPredicate>();
        x.add(new PrologPredicate("X"));
        final List<PrologPredicate> y = new LinkedList<PrologPredicate>();
        y.add(new PrologPredicate("Y"));
        final List<PrologPredicate> xy = new LinkedList<PrologPredicate>();
        xy.add(new PrologPredicate("X"));
        xy.add(new PrologPredicate("Y"));
        final List<PrologPredicate> x1 = new LinkedList<PrologPredicate>();
        x1.add(new PrologPredicate("X"));
        x1.add(new PrologPredicate("1"));

        final PrologPredicate seq = new PrologPredicate("sequential_composition", xy);
        final PrologPredicate dli = new PrologPredicate("defer_lift_invariant", x);
        final PrologPredicate nel = new PrologPredicate("non_electing", x);
        final PrologPredicate def = new PrologPredicate("defers", x1);
        final PrologPredicate ele = new PrologPredicate("electing", y);

        final List<PrologPredicate> param = new LinkedList<PrologPredicate>();
        param.add(seq);

        final PrologPredicate mono = new PrologPredicate("monotone", param);

        final LinkedList<PrologPredicate> antecedents = new LinkedList<PrologPredicate>();
        antecedents.add(dli);
        antecedents.add(nel);
        antecedents.add(def);
        antecedents.add(ele);

        final PrologClause reference = new PrologClause(mono, antecedents);

        final PrologParser parser = new SimplePrologParser();
        final PrologClause res = parser.parseSingleClause(clause);

        assertTrue(res.equals(reference));
    }
}
