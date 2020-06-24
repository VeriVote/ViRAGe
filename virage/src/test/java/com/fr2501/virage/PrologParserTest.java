package com.fr2501.virage;

import static org.junit.Assert.assertTrue;

import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import org.junit.Test;

import com.fr2501.virage.prolog.PrologClause;
import com.fr2501.virage.prolog.PrologParser;
import com.fr2501.virage.prolog.PrologPredicate;
import com.fr2501.virage.prolog.SimplePrologParser;

public class PrologParserTest {
	@Test(expected = IllegalArgumentException.class)
	public void parseEmptyClause() {
		String clause = "";
		PrologParser parser = new SimplePrologParser();
		
		parser.parseSingleClause(clause);
	}
	
	@Test
	public void testEquals() {
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
			List<PrologPredicate> X = new LinkedList<PrologPredicate>();
			X.add(new PrologPredicate("X"));
			List<PrologPredicate> XY = new LinkedList<PrologPredicate>();
			XY.add(new PrologPredicate("X"));
			XY.add(new PrologPredicate("Y"));
			
			PrologPredicate a = new PrologPredicate("a", XY);
			PrologPredicate b = new PrologPredicate("b");
			PrologPredicate c = new PrologPredicate("c", X);
			PrologPredicate d = new PrologPredicate("d", XY);
			
			List<PrologPredicate> antecedents = new LinkedList<PrologPredicate>();
			antecedents.add(b);
			antecedents.add(c);
			antecedents.add(d);
			
			PrologClause clause3 = new PrologClause(a, antecedents);
			assertTrue(clause3.equals(clause3));
		}
		
		{
			List<PrologPredicate> X = new LinkedList<PrologPredicate>();
			X.add(new PrologPredicate("X"));
			List<PrologPredicate> Y = new LinkedList<PrologPredicate>();
			X.add(new PrologPredicate("Y"));
			List<PrologPredicate> XY = new LinkedList<PrologPredicate>();
			XY.add(new PrologPredicate("X"));
			XY.add(new PrologPredicate("Y"));
			List<PrologPredicate> X1 = new LinkedList<PrologPredicate>();
			X1.add(new PrologPredicate("X"));
			X1.add(new PrologPredicate("1"));
			
			PrologPredicate seq = new PrologPredicate("sequential_composition", XY);
			PrologPredicate dli = new PrologPredicate("defer_lift_invariant", X);
			PrologPredicate nel = new PrologPredicate("non_electing", X);
			PrologPredicate ele = new PrologPredicate("electing", Y);
			PrologPredicate def = new PrologPredicate("defers", X1);
			
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
		String clause = "a.";
		PrologClause res = new PrologClause(new PrologPredicate("a"));
		
		PrologParser parser = new SimplePrologParser();
		
		PrologClause parsed = parser.parseSingleClause(clause);
		
		assertTrue(parsed.equals(res));
	}
	
	@Test
	public void parseSimpleClause() {
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
		String clause = "a(X,Y) :- b,c(X),d(X,Y).";
		
		List<PrologPredicate> X = new LinkedList<PrologPredicate>();
		X.add(new PrologPredicate("X"));
		List<PrologPredicate> XY = new LinkedList<PrologPredicate>();
		XY.add(new PrologPredicate("X"));
		XY.add(new PrologPredicate("Y"));
		
		PrologPredicate a = new PrologPredicate("a", XY);
		PrologPredicate b = new PrologPredicate("b");
		PrologPredicate c = new PrologPredicate("c", X);
		PrologPredicate d = new PrologPredicate("d", XY);
		
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
		String clause = "monotone(sequential_composition(X,Y)) :- defer_lift_invariant(X),non_electing(X),defers(X,1),electing(Y).";
		
		List<PrologPredicate> X = new LinkedList<PrologPredicate>();
		X.add(new PrologPredicate("X"));
		List<PrologPredicate> Y = new LinkedList<PrologPredicate>();
		Y.add(new PrologPredicate("Y"));
		List<PrologPredicate> XY = new LinkedList<PrologPredicate>();
		XY.add(new PrologPredicate("X"));
		XY.add(new PrologPredicate("Y"));
		List<PrologPredicate> X1 = new LinkedList<PrologPredicate>();
		X1.add(new PrologPredicate("X"));
		X1.add(new PrologPredicate("1"));
		
		PrologPredicate seq = new PrologPredicate("sequential_composition", XY);
		PrologPredicate dli = new PrologPredicate("defer_lift_invariant", X);
		PrologPredicate nel = new PrologPredicate("non_electing", X);
		PrologPredicate def = new PrologPredicate("defers", X1);
		PrologPredicate ele = new PrologPredicate("electing", Y);
		
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
