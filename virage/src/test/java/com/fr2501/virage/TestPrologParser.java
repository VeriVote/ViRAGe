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

public class TestPrologParser {
	@Test(expected = IllegalArgumentException.class)
	public void parseEmptyClause() {
		String clause = "";
		PrologParser parser = new SimplePrologParser();
		
		parser.parseSingleClause(clause);
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
		Set<PrologPredicate> antecedents = new HashSet<PrologPredicate>();
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
		
		Set<PrologPredicate> antecedents = new HashSet<PrologPredicate>();
		antecedents.add(b);
		antecedents.add(c);
		antecedents.add(d);
		
		PrologClause res = new PrologClause(a, antecedents); 
		
		PrologParser parser = new SimplePrologParser();
		
		PrologClause parse = parser.parseSingleClause(clause);
		
		assertTrue(parse.equals(res));
	}
}
