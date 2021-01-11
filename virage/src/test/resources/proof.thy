theory proof
imports Voting.pass_module Voting.downgrade Voting.plurality_module Voting.parallel_composition Voting.max_aggregator
        Voting.drop_module Voting.loop_composition Voting.defer_eq_condition Voting.elect_module

begin

theorem SMC_monotone:
  assumes order: "linear_order x"
  shows "monotone (SMC x)"
proof -
(* These are some aliases for parts of the sequential majority comparison electoral module. *)
  let ?pass2 = "Pass_module 2 x"
  let ?tie_breaker = "(Pass_module 1 x)"
  let ?plurality_defer = "(Plurality_module\<down>) \<triangleright> ?tie_breaker"
  let ?compare_two = "?pass2 \<triangleright> ?plurality_defer"
  let ?drop2 = "Drop_module 2 x"
  let ?eliminator = "let a = Max_aggregator in ?compare_two \<parallel>\<^sub>a ?drop2"
  let ?loop = "let t = Defer_eq_condition 1 in (?eliminator \<circlearrowleft>\<^sub>t)"

  have 00010: "defer_invariant_monotone (Plurality_module\<down>)"
    by simp (* invariant_monotone_downgrade plurality_strict_strong_mono *)
  have 00011: "non_electing (Plurality_module\<down>)"
    by simp (* minus_1_non_electing plurality_module_sound *)
  have 00012: "non_electing ?tie_breaker"
    by (simp add: order) (* pass_module_non_electing *)
  have 00013: "defers 1 ?tie_breaker"
    using order pass_1_module_defers_1 by simp
  have 00014: "defer_monotone ?tie_breaker"
    by (simp add: order) (* defer_lift_invariant_implies_def_monotone
                            pass_module_defer_lift_invariant *)
  have 20000: "non_blocking (Plurality_module\<down>)"
    by simp (* minus_1_non_blocking plurality_module_electing *)

  have 0000: "defer_lift_invariant ?pass2"
    by (simp add: order) (* pass_module_defer_lift_invariant *)
  have 0001: "defer_lift_invariant ?plurality_defer"
    using 00010 00011 00012 00013 00014 by simp
    (* defer_invariant_monotone_to_defer_lift_invariant *)
  have 0020: "disjoint_compatible ?pass2 ?drop2"
    by (simp add: order) (* disjoint_compatible_commutative drop_pass_compatible *)
  have 1000: "non_electing ?pass2"
    by (simp add: order) (* pass_module_non_electing *)
  have 1001: "non_electing ?plurality_defer"
    using 00011 00012 by simp (* seq_comp_preserves_non_electing *)
  have 2000: "non_blocking ?pass2"
    by (simp add: order) (* pass_module_non_blocking *)
  have 2001: "defers 1 ?plurality_defer"
    using 20000 00011 00013 using seq_comp_defers_1 by blast

  have 000: "defer_lift_invariant ?compare_two"
    using 0000 0001 by simp (* defer_lift_invariant_seq *)
  have 001: "defer_lift_invariant ?drop2"
    by (simp add: order) (* drop_module_defer_lift_invariant *)
  have 002: "disjoint_compatible ?compare_two ?drop2"
    using 0020 by (simp add: order) (* disjoint_compatible_seq seq_creates_modules downgrade_sound
                                       plurality_module_sound pass_module_sound *)
  have 100: "non_electing ?compare_two"
    using 1000 1001 by simp (* seq_comp_preserves_non_electing *)
  have 101: "non_electing ?drop2"
    by (simp add: order) (* drop_module_non_electing *)
  have 102: "conservative Max_aggregator"
    by simp (* max_aggregator_conservative *)
  have 200: "defers 1 ?compare_two"
    using 2000 1000 2001 seq_comp_defers_1 by auto
  have 201: "rejects 2 ?drop2"
    by (simp add: order) (* drop_2_module_rejects_2 *)

  have 00: "defer_lift_invariant ?eliminator"
    using 000 001 002 by simp (* defer_lift_invariant_par *)
  have 10: "non_electing ?eliminator"
    using 100 101 102 by simp (* conservative_agg_comp_preserves_non_electing *)
  have 20: "eliminates 1 ?eliminator"
    using 200 100 201 002 by (meson eliminates_1_par)

  have 0: "defer_lift_invariant ?loop"
    using 00 by simp (* loop_comp_preserves_defer_lift_invariant *)
  have 1: "non_electing ?loop"
    using 10 by simp (* loop_preserves_non_electing *)
  have 2: "defers 1 ?loop"
    using 10 20 by simp (* iterative_elimination_number_of_survivors_for_eliminates *)
  have 3: "electing Elect_module"
    by simp (* elect_module_electing *)

  show ?thesis
    using 0 1 2 3 by (simp add: SMC_def) (* monotone_sequence *)
qed

end
