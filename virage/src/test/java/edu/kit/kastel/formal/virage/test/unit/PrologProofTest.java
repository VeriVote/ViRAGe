package edu.kit.kastel.formal.virage.test.unit;

import static org.junit.Assert.assertTrue;

import org.junit.Test;

import edu.kit.kastel.formal.virage.prolog.PrologProof;

/**
 * Test suite for {@link PrologProof}.
 *
 * @author VeriVote
 */
public class PrologProofTest {
    /**
     * The reference string to compare to.
     */
    private static String reference = "monotone(sequential_composition("
            + "loop_composition(parallel_composition("
            + "sequential_composition(pass_module(2),sequential_composition("
            + "downgrade(plurality_module),pass_module(1))),drop_module(2),max_aggregator),"
            + "defer_eq_condition(1)),elect_module))\n"
            + "\tdefer_lift_invariant(loop_composition(parallel_composition("
            + "sequential_composition(pass_module(2),sequential_"
            + "composition(downgrade(plurality_module),"
            + "pass_module(1)))," + "drop_module(2),max_aggregator),defer_eq_condition(1)))\n"
            + "\t\tdefer_lift_invariant(parallel_composition(sequential_composition("
            + "pass_module(2),sequential_composition(downgrade(plurality_module)"
            + ",pass_module(1))),"
            + "drop_module(2),max_aggregator))\n"
            + "\t\t\tdisjoint_compatible(sequential_composition(pass_module(2)"
            + ",sequential_composition(downgrade(plurality_module),"
            + "pass_module(1))),drop_module(2))\n"
            + "\t\t\t\tdisjoint_compatible(pass_module(2),"
            + "drop_module(2))\n"
            + "\t\t\t\t\tdisjoint_compatible(drop_module(2),"
            + "pass_module(2))\n"
            + "\t\t\tdefer_lift_invariant(sequential_composition(pass_module(2),"
            + "sequential_composition(downgrade(plurality_module),pass_module(1))))\n"
            + "\t\t\t\tdefer_lift_invariant(pass_module(2))\n"
            + "\t\t\t\tdefer_lift_invariant(sequential_composition("
            + "downgrade(plurality_module),pass_module(1)))\n"
            + "\t\t\t\t\tdefer_invariant_monotone(downgrade("
            + "plurality_module))\n"
            + "\t\t\t\t\t\tinvariant_monotone("
            + "plurality_module)\n\t\t\t\t\tnon_electing(pass_module(1))\n"
            + "\t\t\t\t\tdefers(pass_module(1),1)\n"
            + "\t\t\t\t\tdefer_monotone(pass_module(1))\n"
            + "\t\t\t\t\t\tdefer_lift_invariant("
            + "pass_module(1))\n"
            + "\t\t\tdefer_lift_invariant(drop_module(2))\n"
            + "\tnon_electing(loop_composition(parallel_composition("
            + "sequential_composition("
            + "pass_module(2),sequential_composition(downgrade(plurality_module),"
            + "pass_module(1))),drop_module(2),max_aggregator),defer_eq_condition(1)))\n"
            + "\t\tnon_electing(parallel_composition(sequential_composition(pass_module(2),"
            + "sequential_composition(downgrade(plurality_module),"
            + "pass_module(1))),drop_module(2),"
            + "max_aggregator))\n"
            + "\t\t\tnon_electing(sequential_composition(pass_module(2)"
            + ",sequential_composition("
            + "downgrade(plurality_module),pass_module(1))))\n"
            + "\t\t\t\tnon_electing(pass_module(2))\n"
            + "\t\t\t\tnon_electing(sequential_composition("
            + "downgrade(plurality_module),"
            + "pass_module(1)))\n"
            + "\t\t\t\t\tnon_electing(downgrade(plurality_module))\n"
            + "\t\t\t\t\tnon_electing(pass_module(1))\n"
            + "\t\t\tnon_electing(drop_module(2))\n"
            + "\t\t\tconservative(max_aggregator)\n"
            + "\tdefers(loop_composition(parallel_composition("
            + "sequential_composition(pass_module(2),"
            + "sequential_composition(downgrade(plurality_module),pass_module(1))),"
            + "drop_module(2),"
            + "max_aggregator),defer_eq_condition(1)),1)\n\telecting(elect_module)";

    /**
     * The input query.
     */
    private static String input = "subgoal(monotone(sequential_composition("
            + "loop_composition("
            + "parallel_composition(sequential_composition(pass_module(2),"
            + "sequential_composition(downgrade(plurality_module), pass_module(1))),"
            + " drop_module(2), max_aggregator), defer_eq_condition"
            + "(1)), elect_module)),\n','(subgoal(defer_lift_invariant("
            + "loop_composition(parallel_composition(sequential_composition(pass"
            + "_module(2), sequential_composition(downgrade(plurality_module),"
            + " pass_module(1))), drop_module(2), max_aggregator), defer_"
            + "eq_condition(1))),\nsubgoal(defer_lift_invariant(parallel_composition("
            + "sequential_composition(pass_module(2), sequential_c"
            + "omposition(downgrade(plurality_module), pass_module(1))), drop_module(2),"
            + "max_aggregator)),\n','(subgoal(disjoint_compati"
            + "ble(sequential_composition(pass_module(2), sequential_composition(downgrade("
            + "plurality_module)," + " pass_module(1))), drop_mod"
            + "ule(2)),\nsubgoal(disjoint_compatible(pass_module(2), drop_module(2)),\nsubgoal("
            + "disjoint_compatible(drop_module(2), pass_"
            + "module(2)), true))), \n','(subgoal(defer_lift_invariant(sequential_composition("
            + "pass_module(2), sequential_composition(dow"
            + "ngrade(plurality_module), pass_module(1)))), \n','(subgoal(defer_lift_invariant("
            + "pass_module(2)), true),\nsubgoal(defer_li"
            + "ft_invariant(sequential_composition(downgrade(plurality_module),"
            + " pass_module(1))),"
            + " \n','(subgoal(defer_invariant_monotone"
            + "(downgrade(plurality_module)),\nsubgoal(invariant_monotone("
            + "plurality_module), true)),"
            + " \n','(subgoal(non_electing(pass_mod"
            + "ule(1)), true), \n','(subgoal(defers(pass_module(1), 1), true),"
            + "\nsubgoal(defer_monotone("
            + "pass_module(1)), \nsubgoal(defer_"
            + "lift_invariant(pass_module(1)), true)))))))), \nsubgoal(defer_lift_invariant("
            + "drop_module(2)), true))))), \n','(subgoal(no"
            + "n_electing(loop_composition(parallel_composition(sequential_composition("
            + "pass_module(2), sequential_composition(downgrade("
            + "plurality_module), pass_module(1))), drop_module(2), max_aggregator), "
            + "defer_eq_condition(1))), \nsubgoal(non_electing(par"
            + "allel_composition(sequential_composition(pass_module(2), sequential_composition("
            + "downgrade(plurality_module), pass_module("
            + "1))), drop_module(2), max_aggregator)), \n','(subgoal(non_electing("
            + "sequential_composition(pass_module(2), sequential_comp"
            + "osition(downgrade(plurality_module), pass_module(1)))), \n','(subgoal("
            + "non_electing(pass_module(2)), true), \nsubgoal(non_"
            + "electing(sequential_composition(downgrade(plurality_module), pass_module(1))), "
            + "\n','(subgoal(non_electing(downgrade(plura"
            + "lity_module)), true), \nsubgoal(non_electing(pass_module(1)), true))))), \n"
            + "','(subgoal(non_electing(drop_module(2)), true"
            + "), \nsubgoal(conservative(max_aggregator), true))))), \n','(subgoal(defers("
            + "loop_composition(parallel_composition(sequenti"
            + "al_composition(pass_module(2), sequential_composition("
            + "downgrade(plurality_module), pass_module(1))), drop_module(2), max_"
            + "aggregator), defer_eq_condition(1)), 1), true), \nsubgoal("
            + "electing(elect_module), true)))))";

    /**
     * Tries to derive a proof of SMC's monotonicity.
     */
    @Test
    public void testSmcMonotone() {
        final PrologProof proof = PrologProof.createProofFromString(input);
        assertTrue(proof.toString().equals(reference));
    }
}
