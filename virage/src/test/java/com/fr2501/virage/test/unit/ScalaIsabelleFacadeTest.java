package com.fr2501.virage.test.unit;

import static org.junit.Assert.fail;

import org.junit.Test;

import com.fr2501.virage.isabelle.ScalaIsabelleFacade;

public class ScalaIsabelleFacadeTest {
	@Test
	public void simpleTest() {
		ScalaIsabelleFacade facade = new ScalaIsabelleFacade(
				"src/test/resources/verifiedVotingRuleConstruction/theories",
				"Verified_Voting_Rule_Construction");
	}
}
