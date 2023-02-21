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
     * Test Prolog predicate name "".
     */
    private static final String EMPTY = "";

    /**
     * Test Prolog predicate name ",".
     */
    private static final String COMMA = ",";

    /**
     * Test Prolog predicate name "a".
     */
    private static final String A = "a";

    /**
     * Test Prolog predicate name "b".
     */
    private static final String B = "b";

    /**
     * Test Prolog predicate name "c".
     */
    private static final String C = "c";

    /**
     * Test Prolog predicate name "d".
     */
    private static final String D = "d";

    /**
     * Test Prolog predicate name "X".
     */
    private static final String X = "X";

    /**
     * Test Prolog predicate name "Y".
     */
    private static final String Y = "Y";

    /**
     * Test Prolog predicate name "1".
     */
    private static final String ONE = "1";

    /**
     * Test Prolog predicate name "sequential_composition".
     */
    private static final String SEQ_COMP = "sequential_composition";

    /**
     * Test Prolog predicate name "defer_lift_invariance".
     */
    private static final String DEFER_LIFT_INV = "defer_lift_invariance";

    /**
     * Test Prolog predicate name "non_electing".
     */
    private static final String NON_ELECTING = "non_electing";

    /**
     * Test Prolog predicate name "electing".
     */
    private static final String ELECTING = "electing";

    /**
     * Test Prolog predicate name "defers".
     */
    private static final String DEFERS = "defers";

    /**
     * Test Prolog predicate name "monotonicity".
     */
    private static final String MONO = "monotonicity";

    /**
     * The logger.
     */
    private static final Logger LOGGER = LogManager.getLogger(PrologParserTest.class);

    /**
     * Translates a predicate to a test Prolog fact.
     *
     * @param pred the predicate of the composed fact
     * @return a test String representing the composed Prolog fact
     */
    private static String fact(final String pred) {
        return pred + ".";
    }

    /**
     * Translates a predicate name and arguments to a test Prolog predicate.
     *
     * @param name the predicate name of the composed predicate
     * @param args the predicate's arguments
     * @return a test String representing the composed Prolog predicate
     */
    private static String predicate(final String name, final String... args) {
        String arg = EMPTY;
        for (final String a : args) {
            if (!arg.isEmpty()) {
                arg += COMMA;
            }
            arg += a;
        }
        return "name" + "(" + arg + ")";
    }

    /**
     * Translates a head predicate and various body predicates to a test Prolog clause.
     *
     * @param head the head predicate of the composed clause
     * @param args the body predicates in the resulting clause
     * @return a test String representing the composed Prolog clause
     */
    private static String clause(final String head, final String... args) {
        final String sign = " :- ";
        String body = EMPTY;
        for (final String b : args) {
            if (!body.isEmpty()) {
                body += COMMA;
            }
            body += b;
        }
        return fact(head + sign + body);
    }

    /**
     * Tests behavior on empty clause.
     */
    @Test(expected = IllegalArgumentException.class)
    public void parseEmptyClause() {
        LOGGER.info("parseEmptyClause()");
        final String clause = EMPTY;
        final PrologParser parser = new SimplePrologParser();

        parser.parseSingleClause(clause);
    }

    /**
     * Tests equality of parsed clauses.
     */
    @Test
    public void testEquals() {
        LOGGER.info("testEquals()");

        final PrologClause clause1 = new PrologClause(new PrologPredicate(A));
        assertTrue(clause1.equals(clause1));

        final LinkedList<PrologPredicate> antecedents1 = new LinkedList<PrologPredicate>();
        antecedents1.add(new PrologPredicate(B));
        antecedents1.add(new PrologPredicate(C));
        final PrologClause clause2 = new PrologClause(new PrologPredicate(A), antecedents1);
        assertTrue(clause2.equals(clause2));

        final List<PrologPredicate> x = new LinkedList<PrologPredicate>();
        x.add(new PrologPredicate(X));
        final List<PrologPredicate> xy = new LinkedList<PrologPredicate>();
        xy.add(new PrologPredicate(X));
        xy.add(new PrologPredicate(Y));

        final PrologPredicate a = new PrologPredicate(A, xy);
        final PrologPredicate b = new PrologPredicate(B);
        final PrologPredicate c = new PrologPredicate(C, x);
        final PrologPredicate d = new PrologPredicate(D, xy);

        final List<PrologPredicate> antecedents2 = new LinkedList<PrologPredicate>();
        antecedents2.add(b);
        antecedents2.add(c);
        antecedents2.add(d);

        final PrologClause clause3 = new PrologClause(a, antecedents2);
        assertTrue(clause3.equals(clause3));

        final List<PrologPredicate> x2 = new LinkedList<PrologPredicate>();
        x2.add(new PrologPredicate(X));
        final List<PrologPredicate> y = new LinkedList<PrologPredicate>();
        x2.add(new PrologPredicate(Y));
        final List<PrologPredicate> xy2 = new LinkedList<PrologPredicate>();
        xy2.add(new PrologPredicate(X));
        xy2.add(new PrologPredicate(Y));
        final List<PrologPredicate> x1 = new LinkedList<PrologPredicate>();
        x1.add(new PrologPredicate(X));
        x1.add(new PrologPredicate(ONE));

        final PrologPredicate seq = new PrologPredicate(SEQ_COMP, xy2);
        final PrologPredicate dli = new PrologPredicate(DEFER_LIFT_INV, x2);
        final PrologPredicate nel = new PrologPredicate(NON_ELECTING, x2);
        final PrologPredicate ele = new PrologPredicate(ELECTING, y);
        final PrologPredicate def = new PrologPredicate(DEFERS, x1);

        final List<PrologPredicate> param = new LinkedList<PrologPredicate>();
        param.add(seq);

        final PrologPredicate mono = new PrologPredicate(MONO, param);

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
        final String clause = fact(A);
        final PrologClause res = new PrologClause(new PrologPredicate(A));

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
        final String clause = clause(A, B, C);
        final List<PrologPredicate> antecedents = new LinkedList<PrologPredicate>();
        antecedents.add(new PrologPredicate(B));
        antecedents.add(new PrologPredicate(C));
        final PrologClause res = new PrologClause(new PrologPredicate(A), antecedents);

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
        final String clause = clause(predicate(A, X, Y), B, predicate(C, X), predicate(D, X, Y));

        final List<PrologPredicate> x = new LinkedList<PrologPredicate>();
        x.add(new PrologPredicate(X));
        final List<PrologPredicate> xy = new LinkedList<PrologPredicate>();
        xy.add(new PrologPredicate(X));
        xy.add(new PrologPredicate(Y));

        final PrologPredicate a = new PrologPredicate(A, xy);
        final PrologPredicate b = new PrologPredicate(B);
        final PrologPredicate c = new PrologPredicate(C, x);
        final PrologPredicate d = new PrologPredicate(D, xy);

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
        final String clause =
            clause(predicate(MONO, predicate(SEQ_COMP, X, Y)), predicate(DEFER_LIFT_INV, X),
                   predicate(NON_ELECTING, X), predicate(DEFERS, X, ONE), predicate(ELECTING, Y));

        final List<PrologPredicate> x = new LinkedList<PrologPredicate>();
        x.add(new PrologPredicate(X));
        final List<PrologPredicate> y = new LinkedList<PrologPredicate>();
        y.add(new PrologPredicate(Y));
        final List<PrologPredicate> xy = new LinkedList<PrologPredicate>();
        xy.add(new PrologPredicate(X));
        xy.add(new PrologPredicate(Y));
        final List<PrologPredicate> x1 = new LinkedList<PrologPredicate>();
        x1.add(new PrologPredicate(X));
        x1.add(new PrologPredicate(ONE));

        final PrologPredicate seq = new PrologPredicate(SEQ_COMP, xy);
        final PrologPredicate dli = new PrologPredicate(DEFER_LIFT_INV, x);
        final PrologPredicate nel = new PrologPredicate(NON_ELECTING, x);
        final PrologPredicate def = new PrologPredicate(DEFERS, x1);
        final PrologPredicate ele = new PrologPredicate(ELECTING, y);

        final List<PrologPredicate> param = new LinkedList<PrologPredicate>();
        param.add(seq);

        final PrologPredicate mono = new PrologPredicate(MONO, param);

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
