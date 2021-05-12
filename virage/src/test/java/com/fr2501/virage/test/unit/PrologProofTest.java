package com.fr2501.virage.test.unit;

import static org.junit.Assert.assertTrue;

import org.junit.Test;

import com.fr2501.virage.prolog.PrologProof;

public class PrologProofTest {
  @Test
  public void testSMCMonotone() {
    String input = "subgoal(monotone(sequential_composition(loop_composition(parallel_composition(sequential_composition(pass_module(2),"
        + "sequential_composition(downgrade(plurality_module), pass_module(1))), drop_module(2), max_aggregator), defer_eq_condition"
        + "(1)), elect_module)),\n','(subgoal(defer_lift_invariant(loop_composition(parallel_composition(sequential_composition(pass"
        + "_module(2), sequential_composition(downgrade(plurality_module), pass_module(1))), drop_module(2), max_aggregator), defer_"
        + "eq_condition(1))),\nsubgoal(defer_lift_invariant(parallel_composition(sequential_composition(pass_module(2), sequential_c"
        + "omposition(downgrade(plurality_module), pass_module(1))), drop_module(2), max_aggregator)),\n','(subgoal(disjoint_compati"
        + "ble(sequential_composition(pass_module(2), sequential_composition(downgrade(plurality_module), pass_module(1))), drop_mod"
        + "ule(2)),\nsubgoal(disjoint_compatible(pass_module(2), drop_module(2)),\nsubgoal(disjoint_compatible(drop_module(2), pass_"
        + "module(2)), true))), \n','(subgoal(defer_lift_invariant(sequential_composition(pass_module(2), sequential_composition(dow"
        + "ngrade(plurality_module), pass_module(1)))), \n','(subgoal(defer_lift_invariant(pass_module(2)), true),\nsubgoal(defer_li"
        + "ft_invariant(sequential_composition(downgrade(plurality_module), pass_module(1))), \n','(subgoal(defer_invariant_monotone"
        + "(downgrade(plurality_module)),\nsubgoal(invariant_monotone(plurality_module), true)), \n','(subgoal(non_electing(pass_mod"
        + "ule(1)), true), \n','(subgoal(defers(pass_module(1), 1), true),\nsubgoal(defer_monotone(pass_module(1)), \nsubgoal(defer_"
        + "lift_invariant(pass_module(1)), true)))))))), \nsubgoal(defer_lift_invariant(drop_module(2)), true))))), \n','(subgoal(no"
        + "n_electing(loop_composition(parallel_composition(sequential_composition(pass_module(2), sequential_composition(downgrade("
        + "plurality_module), pass_module(1))), drop_module(2), max_aggregator), defer_eq_condition(1))), \nsubgoal(non_electing(par"
        + "allel_composition(sequential_composition(pass_module(2), sequential_composition(downgrade(plurality_module), pass_module("
        + "1))), drop_module(2), max_aggregator)), \n','(subgoal(non_electing(sequential_composition(pass_module(2), sequential_comp"
        + "osition(downgrade(plurality_module), pass_module(1)))), \n','(subgoal(non_electing(pass_module(2)), true), \nsubgoal(non_"
        + "electing(sequential_composition(downgrade(plurality_module), pass_module(1))), \n','(subgoal(non_electing(downgrade(plura"
        + "lity_module)), true), \nsubgoal(non_electing(pass_module(1)), true))))), \n','(subgoal(non_electing(drop_module(2)), true"
        + "), \nsubgoal(conservative(max_aggregator), true))))), \n','(subgoal(defers(loop_composition(parallel_composition(sequenti"
        + "al_composition(pass_module(2), sequential_composition(downgrade(plurality_module), pass_module(1))), drop_module(2), max_"
        + "aggregator), defer_eq_condition(1)), 1), true), \nsubgoal(electing(elect_module), true)))))";

    String reference = "monotone(sequential_composition(loop_composition(parallel_composition(sequential_composition(pass_module(2),sequential_composition(downgrade(plurality_module),pass_module(1))),drop_module(2),max_aggregator),defer_eq_condition(1)),elect_module))\n"
        + "	defer_lift_invariant(loop_composition(parallel_composition(sequential_composition(pass_module(2),sequential_composition(downgrade(plurality_module),pass_module(1))),drop_module(2),max_aggregator),defer_eq_condition(1)))\n"
        + "		defer_lift_invariant(parallel_composition(sequential_composition(pass_module(2),sequential_composition(downgrade(plurality_module),pass_module(1))),drop_module(2),max_aggregator))\n"
        + "			disjoint_compatible(sequential_composition(pass_module(2),sequential_composition(downgrade(plurality_module),pass_module(1))),drop_module(2))\n"
        + "				disjoint_compatible(pass_module(2),drop_module(2))\n"
        + "					disjoint_compatible(drop_module(2),pass_module(2))\n"
        + "			defer_lift_invariant(sequential_composition(pass_module(2),sequential_composition(downgrade(plurality_module),pass_module(1))))\n"
        + "				defer_lift_invariant(pass_module(2))\n"
        + "				defer_lift_invariant(sequential_composition(downgrade(plurality_module),pass_module(1)))\n"
        + "					defer_invariant_monotone(downgrade(plurality_module))\n"
        + "						invariant_monotone(plurality_module)\n" + "					non_electing(pass_module(1))\n"
        + "					defers(pass_module(1),1)\n" + "					defer_monotone(pass_module(1))\n"
        + "						defer_lift_invariant(pass_module(1))\n" + "			defer_lift_invariant(drop_module(2))\n"
        + "	non_electing(loop_composition(parallel_composition(sequential_composition(pass_module(2),sequential_composition(downgrade(plurality_module),pass_module(1))),drop_module(2),max_aggregator),defer_eq_condition(1)))\n"
        + "		non_electing(parallel_composition(sequential_composition(pass_module(2),sequential_composition(downgrade(plurality_module),pass_module(1))),drop_module(2),max_aggregator))\n"
        + "			non_electing(sequential_composition(pass_module(2),sequential_composition(downgrade(plurality_module),pass_module(1))))\n"
        + "				non_electing(pass_module(2))\n"
        + "				non_electing(sequential_composition(downgrade(plurality_module),pass_module(1)))\n"
        + "					non_electing(downgrade(plurality_module))\n" + "					non_electing(pass_module(1))\n"
        + "			non_electing(drop_module(2))\n" + "			conservative(max_aggregator)\n"
        + "	defers(loop_composition(parallel_composition(sequential_composition(pass_module(2),sequential_composition(downgrade(plurality_module),pass_module(1))),drop_module(2),max_aggregator),defer_eq_condition(1)),1)\n"
        + "	electing(elect_module)";

    PrologProof proof = PrologProof.createProofFromString(input);

    assertTrue(proof.toString().equals(reference));
  }
}
