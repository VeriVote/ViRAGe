% ==== ./src/test/resources/verifiedVotingRuleConstruction/theories/ - Verified_Voting_Rule_Construction
%
% === component_type
% == Set.set(?'a)
% == Aggregator
% max_aggregator()
% == List.list(?'a)
% == composable_module
% == Preference_Relation
% == Profile
% == Rel.rel(?'a)
% == HOL.bool
% == Electoral_Module
% copeland_rule()
% minimax()
% less_eliminator(Evaluation_Function,Nat.nat)
% min_eliminator(Evaluation_Function)
% elimination_module(Evaluation_Function,Nat.nat,Nat.nat,Nat.nat,HOL.bool)
% pass_module(Nat.nat,Preference_Relation)
% less_average_eliminator(Evaluation_Function)
% minimax_rule()
% schwartz_rule()
% pairwise_majority_rule'()
% classic_nanson_rule()
% smc(Preference_Relation)
% condorcet()
% condorcet'()
% leq_eliminator(Evaluation_Function,Nat.nat)
% copeland()
% blacks_rule()
% plurality()
% max_eliminator(Evaluation_Function)
% defer_module()
% leq_average_eliminator(Evaluation_Function)
% pairwise_majority_rule()
% borda_rule()
% drop_module(Nat.nat,Preference_Relation)
% nanson_baldwin_rule()
% elect_module()
% borda()
% == Nat.nat
% prefer_count(Profile,?'a,?'a)
% win_count(Profile,?'a)
% average(Evaluation_Function,Set.set(?'a),Profile)
% prefer_count_code(Profile,?'a,?'a)
% win_count_code(Profile,?'a)
% rank(Preference_Relation,?'a)
% == Termination_Condition
% defer_equal_condition(Nat.nat)
% disjoint3()
% set_equals_partition(Set.set(?'a))
% well_formed(Set.set(?'a))
% == ?'a
% == Evaluation_Function
% borda_score()
% copeland_score()
% condorcet_score()
% minimax_score()
%
% === composable_module
%% This area is deprecated and therefore intentionally empty.
% === compositional_structure
% iterelect(Electoral_Module)
% elimination_set(Evaluation_Function,Nat.nat,Nat.nat,Nat.nat,HOL.bool,Set.set(?'a),Profile)
% sequential_composition(Electoral_Module,Electoral_Module)
% loop_composition(Electoral_Module,Termination_Condition)
% elector(Electoral_Module)
% limit_profile(Set.set(?'a),Profile)
% iter(Electoral_Module)
% maximum_parallel_composition(Electoral_Module,Electoral_Module)
% parallel_composition(Electoral_Module,Electoral_Module,Aggregator)
% times(Nat.nat,List.list(?'a))
% revision_composition(Electoral_Module)
% limit(Set.set(?'a),Preference_Relation)
% loop_comp_helper(Electoral_Module,Electoral_Module,Termination_Condition)
%
% === property
% defer_condorcet_consistency(Electoral_Module)
% wins(?'a,Profile,?'a)
% is_less_preferred_than(?'a,Preference_Relation,?'a)
% aggregator(Aggregator)
% linear_order(Rel.rel(?'a))
% condorcet_compatibility(Electoral_Module)
% defer_invariant_monotonicity(Electoral_Module)
% indep_of_alt(Electoral_Module,Set.set(?'a),?'a)
% prof_contains_result(Electoral_Module,Set.set(?'a),Profile,Profile,?'a)
% non_blocking(Electoral_Module)
% defer_deciding(Electoral_Module)
% agg_commutative(Aggregator)
% condorcet_rating(Evaluation_Function)
% rejects(Nat.nat,Electoral_Module)
% invariant_monotonicity(Electoral_Module)
% agg_conservative(Aggregator)
% trans(Rel.rel(?'a))
% electoral_module(Electoral_Module)
% connex(Set.set(?'a),Preference_Relation)
% defers(Nat.nat,Electoral_Module)
% lifted(Set.set(?'a),Preference_Relation,Preference_Relation,?'a)
% limited(Set.set(?'a),Preference_Relation)
% profile(Set.set(?'a),Profile)
% electing(Electoral_Module)
% non_electing(Electoral_Module)
% defer_lift_invariance(Electoral_Module)
% monotonicity(Electoral_Module)
% prof_geq_result(Electoral_Module,Set.set(?'a),Profile,Profile,?'a)
% equiv_prof_except_a(Set.set(?'a),Profile,Profile,?'a)
% homogeneity(Electoral_Module)
% prof_leq_result(Electoral_Module,Set.set(?'a),Profile,Profile,?'a)
% mod_contains_result(Electoral_Module,Electoral_Module,Set.set(?'a),Profile,?'a)
% defer_monotonicity(Electoral_Module)
% eliminates(Nat.nat,Electoral_Module)
% decrementing(Electoral_Module)
% disjoint_compatibility(Electoral_Module,Electoral_Module)
% elects(Nat.nat,Electoral_Module)
% condorcet_consistency(Electoral_Module)
% finite_profile(Set.set(?'a),Profile)
% equiv_rel_except_a(Set.set(?'a),Preference_Relation,Preference_Relation,?'a)
% condorcet_winner(Set.set(?'a),Profile,?'a)
% linear_order(Rel.rel(?'a))
% trans(Rel.rel(?'a))
% finite_profile(Set.set(?'a),Profile)
%
% === composition_rule
% = Aggregator_Facts.thy
% Aggregator_Facts.max_agg_comm
agg_commutative(max_aggregator).

% = Aggregator_Facts.thy
% Aggregator_Facts.max_agg_consv
agg_conservative(max_aggregator).

% = Maximum_Aggregator.thy
% Maximum_Aggregator.max_agg_sound
aggregator(max_aggregator).

% = Preference_Relation.thy
% Preference_Relation.lin_imp_antisym
antisym(R) :- linear_order_on(A,R).

% = Condorcet_Rules.thy
% Condorcet_Rules.cr_eval_imp_ccomp_max_elim
condorcet_compatibility(max_eliminator(E)) :- finite_profile(A,P),condorcet_rating(E).

% = Minimax_Rule.thy
% Minimax_Rule.minimax_condorcet
condorcet_consistency(minimax_rule).

% = Copeland_Rule.thy
% Copeland_Rule.copeland_condorcet
condorcet_consistency(copeland_rule).

% = Pairwise_Majority_Rule.thy
% Pairwise_Majority_Rule.condorcet_condorcet
condorcet_consistency(pairwise_majority_rule).

% = Condorcet_Rules.thy
% Condorcet_Rules.dcc_imp_cc_elector
condorcet_consistency(elector(M)) :- defer_condorcet_consistency(M).

% = Condorcet_Facts.thy
% Condorcet_Facts.minimax_score_cond_rating
condorcet_rating(minimax_score).

% = Condorcet_Facts.thy
% Condorcet_Facts.condorcet_score_is_condorcet_rating
condorcet_rating(condorcet_score).

% = Condorcet_Facts.thy
% Condorcet_Facts.copeland_score_is_cr
condorcet_rating(copeland_score).

% = generated
% condorcet_winner_intro
condorcet_winner(_,_,_).

% = generated
% connex_intro
connex(_,_).

% = Preference_Relation.thy
% Preference_Relation.lin_ord_imp_connex
connex(A,R) :- linear_order_on(A,R).

% = Condorcet_Facts.thy
% Condorcet_Facts.copeland_is_dcc
defer_condorcet_consistency(copeland).

% = Condorcet_Facts.thy
% Condorcet_Facts.condorcet_is_dcc
defer_condorcet_consistency(condorcet).

% = Condorcet_Facts.thy
% Condorcet_Facts.minimax_is_dcc
defer_condorcet_consistency(minimax).

% = Condorcet_Rules.thy
% Condorcet_Rules.cr_eval_imp_dcc_max_elim
defer_condorcet_consistency(max_eliminator(E)) :- condorcet_rating(E).

% = Condorcet_Rules.thy
% Condorcet_Rules.ccomp_and_dd_imp_dcc
defer_condorcet_consistency(M) :- condorcet_compatibility(M),defer_deciding(M).

% = Monotonicity_Rules.thy
% Monotonicity_Rules.rev_comp_def_inv_mono
defer_invariant_monotonicity(revision_composition(M)) :- invariant_monotonicity(M).

% = Monotonicity_Facts.thy
% Monotonicity_Facts.def_mod_def_lift_inv
defer_lift_invariance(defer_module).

% = Monotonicity_Rules.thy
% Monotonicity_Rules.loop_comp_presv_def_lift_inv
defer_lift_invariance(loop_composition(M,T)) :- defer_lift_invariance(M).

% = Monotonicity_Facts.thy
% Monotonicity_Facts.pass_mod_dl_inv
defer_lift_invariance(pass_module(N,R)) :- linear_order(R).

% = Monotonicity_Facts.thy
% Monotonicity_Facts.drop_mod_def_lift_inv
defer_lift_invariance(drop_module(N,R)) :- linear_order(R).

% = Monotonicity_Rules.thy
% Monotonicity_Rules.seq_comp_presv_def_lift_inv
defer_lift_invariance(sequential_composition(M,N)) :- defer_lift_invariance(M),defer_lift_invariance(N).

% = Monotonicity_Rules.thy
% Monotonicity_Rules.loop_comp_helper_presv_def_lift_inv
defer_lift_invariance(loop_comp_helper(ACC,M,T)) :- defer_lift_invariance(M),defer_lift_invariance(ACC).

% = Monotonicity_Rules.thy
% Monotonicity_Rules.par_comp_def_lift_inv
defer_lift_invariance(maximum_parallel_composition(M,N)) :- disjoint_compatibility(M,N),defer_lift_invariance(M),defer_lift_invariance(N).

% = Monotonicity_Rules.thy
% Monotonicity_Rules.def_inv_mono_imp_def_lift_inv
defer_lift_invariance(sequential_composition(M,N)) :- defer_invariant_monotonicity(M),non_electing(N),defers(1,N),defer_monotonicity(N).

% = Monotonicity_Rules.thy
% Monotonicity_Rules.dl_inv_imp_def_mono
defer_monotonicity(M) :- defer_lift_invariance(M).

% = Result_Facts.thy
% Result_Facts.pass_zero_mod_def_zero
defers(0,pass_module(0,R)) :- linear_order(R).

% = Result_Facts.thy
% Result_Facts.pass_one_mod_def_one
defers(1,pass_module(1,R)) :- linear_order(R).

% = Result_Facts.thy
% Result_Facts.pass_two_mod_def_two
defers(2,pass_module(2,R)) :- linear_order(R).

% = Result_Rules.thy
% Result_Rules.seq_comp_def_one
defers(1,sequential_composition(M,N)) :- non_blocking(M),non_electing(M),defers(1,N).

% = Sequential_Composition.thy
% Sequential_Composition.seq_comp_presv_disj
disjoint3(sequential_composition(M,N,A,P)) :- electoral_module(M),electoral_module(N),finite_profile(A,P).

% = Disjoint_Compatibility_Facts.thy
% Disjoint_Compatibility_Facts.drop_pass_disj_compat
disjoint_compatibility(drop_module(N,R),pass_module(N,R)) :- linear_order(R).

% = Disjoint_Compatibility_Rules.thy
% Disjoint_Compatibility_Rules.disj_compat_comm
disjoint_compatibility(N,M) :- disjoint_compatibility(M,N).

% = Result_Facts.thy
% Result_Facts.plurality_electing
electing(plurality).

% = Result_Facts.thy
% Result_Facts.elect_mod_electing
electing(elect_module).

% = Sequential_Majority_Comparison.thy
% Sequential_Majority_Comparison.smc_electing
electing(smc(X)) :- linear_order(X).

% = Result_Rules.thy
% Result_Rules.elector_electing
electing(elector(M)) :- electoral_module(M),non_blocking(M).

% = Elect_Module.thy
% Elect_Module.elect_mod_sound
electoral_module(elect_module).

% = Defer_Module.thy
% Defer_Module.def_mod_sound
electoral_module(defer_module).

% = Elimination_Module.thy
% Elimination_Module.less_elim_sound
electoral_module(less_eliminator(E,T)).

% = Elimination_Module.thy
% Elimination_Module.leq_elim_sound
electoral_module(leq_eliminator(E,T)).

% = Elimination_Module.thy
% Elimination_Module.leq_avg_elim_sound
electoral_module(leq_average_eliminator(E)).

% = Elimination_Module.thy
% Elimination_Module.elim_mod_sound
electoral_module(elimination_module(E,T,R)).

% = Elimination_Module.thy
% Elimination_Module.max_elim_sound
electoral_module(max_eliminator(E)).

% = Elimination_Module.thy
% Elimination_Module.min_elim_sound
electoral_module(min_eliminator(E)).

% = Elimination_Module.thy
% Elimination_Module.less_avg_elim_sound
electoral_module(less_average_eliminator(E)).

% = Plurality_Module.thy
% Plurality_Module.plurality_sound
electoral_module(plurality).

% = Loop_Composition.thy
% Loop_Composition.loop_comp_sound
electoral_module(loop_composition(M,T)) :- electoral_module(M).

% = Revision_Composition.thy
% Revision_Composition.rev_comp_sound
electoral_module(revision_composition(M)) :- electoral_module(M).

% = Pass_Module.thy
% Pass_Module.pass_mod_sound
electoral_module(pass_module(N,R)) :- linear_order(R).

% = Sequential_Majority_Comparison.thy
% Sequential_Majority_Comparison.smc_sound
electoral_module(smc(X)) :- linear_order(X).

% = Drop_Module.thy
% Drop_Module.drop_mod_sound
electoral_module(drop_module(N,R)) :- linear_order(R).

% = Composite_Structures.thy
% Composite_Structures.elector_sound
electoral_module(elector(M)) :- electoral_module(M).

% = Sequential_Composition.thy
% Sequential_Composition.seq_comp_sound
electoral_module(sequential_composition(M,N)) :- electoral_module(M),electoral_module(N).

% = Composite_Structures.thy
% Composite_Structures.max_par_comp_sound
electoral_module(maximum_parallel_composition(M,N)) :- electoral_module(M),electoral_module(N).

% = Parallel_Composition.thy
% Parallel_Composition.par_comp_sound
electoral_module(parallel_composition(M,N,A)) :- electoral_module(M),electoral_module(N),aggregator(A).

% = Result_Rules.thy
% Result_Rules.par_comp_elim_one
eliminates(1,maximum_parallel_composition(M,N)) :- defers(1,M),non_electing(M),rejects(2,N),disjoint_compatibility(M,N).

% = generated
% equiv_prof_except_a_intro
equiv_prof_except_a(_,_,_,_).

% = Profile.thy
% Profile.lifted_imp_equiv_prof_except_a
equiv_prof_except_a(A,P,Q,A) :- lifted(A,P,Q,A).

% = generated
% equiv_rel_except_a_intro
equiv_rel_except_a(_,_,_,_).

% = Preference_Relation.thy
% Preference_Relation.lifted_imp_equiv_rel_except_a
equiv_rel_except_a(A,R,S,A) :- lifted(A,R,S,A).

% = generated
% finite_profile_intro
finite_profile(_,_).

% = Monotonicity_Facts.thy
% Monotonicity_Facts.plurality_inv_mono
invariant_monotonicity(plurality).

% = generated
% is_less_preferred_than_intro
is_less_preferred_than(_,_,_).

% = Preference_Relation.thy
% Preference_Relation.lifted_mono2
is_less_preferred_than(X,S,A) :- lifted(A,R,S,A),is_less_preferred_than(X,R,A).

% = generated
% lifted_intro
lifted(_,_,_,_).

% = generated
% limited_intro
limited(_,_).

% = Preference_Relation.thy
% Preference_Relation.limit_to_limits
limited(A,limit(A,R)).

% = generated
% linear_order_intro
linear_order(_).

% = Preference_Relation.thy
% Preference_Relation.connex_antsym_and_trans_imp_lin_ord
linear_order_on(A,R) :- connex(A,R),antisym(R),trans(R).

% = Electoral_Module.thy
% Electoral_Module.mod_contains_result_comm
mod_contains_result(N,M,A,P,A) :- mod_contains_result(M,N,A,P,A).

% = Sequential_Majority_Comparison.thy
% Sequential_Majority_Comparison.smc_monotone
monotonicity(smc(X)) :- linear_order(X).

% = Monotonicity_Rules.thy
% Monotonicity_Rules.seq_comp_mono
monotonicity(sequential_composition(M,N)) :- defer_lift_invariance(M),non_electing(M),defers(1,M),electing(N).

% = Result_Rules.thy
% Result_Rules.electing_imp_non_blocking
non_blocking(M) :- electing(M).

% = Result_Rules.thy
% Result_Rules.seq_comp_presv_non_blocking
non_blocking(sequential_composition(M,N)) :- non_blocking(M),non_blocking(N).

% = Result_Facts.thy
% Result_Facts.def_mod_non_electing
non_electing(defer_module).

% = Result_Rules.thy
% Result_Rules.loop_comp_presv_non_electing
non_electing(loop_composition(M,T)) :- non_electing(M).

% = Result_Facts.thy
% Result_Facts.drop_mod_non_electing
non_electing(drop_module(N,R)) :- linear_order(R).

% = Result_Facts.thy
% Result_Facts.less_elim_non_electing
non_electing(less_eliminator(E,T)) :- finite_profile(A,P).

% = Result_Facts.thy
% Result_Facts.less_avg_elim_non_electing
non_electing(less_average_eliminator(E)) :- finite_profile(A,P).

% = Result_Facts.thy
% Result_Facts.leq_elim_non_electing
non_electing(leq_eliminator(E,T)) :- finite_profile(A,P).

% = Result_Facts.thy
% Result_Facts.min_elim_non_electing
non_electing(min_eliminator(E)) :- finite_profile(A,P).

% = Result_Facts.thy
% Result_Facts.elim_mod_non_electing
non_electing(elimination_module(E,T,R)) :- finite_profile(A,P).

% = Result_Facts.thy
% Result_Facts.rev_comp_non_electing
non_electing(revision_composition(M)) :- electoral_module(M).

% = Result_Facts.thy
% Result_Facts.pass_mod_non_electing
non_electing(pass_module(N,R)) :- linear_order(R).

% = Result_Facts.thy
% Result_Facts.max_elim_non_electing
non_electing(max_eliminator(E)) :- finite_profile(A,P).

% = Result_Facts.thy
% Result_Facts.leq_avg_elim_non_electing
non_electing(leq_average_eliminator(E)) :- finite_profile(A,P).

% = Result_Rules.thy
% Result_Rules.seq_comp_presv_non_electing
non_electing(sequential_composition(M,N)) :- non_electing(M),non_electing(N).

% = Result_Rules.thy
% Result_Rules.conserv_max_agg_presv_non_electing
non_electing(maximum_parallel_composition(M,N)) :- non_electing(M),non_electing(N).

% = Result_Rules.thy
% Result_Rules.conserv_agg_presv_non_electing
non_electing(parallel_composition(M,N,A)) :- non_electing(M),non_electing(N),agg_conservative(A).

% = generated
% profile_intro
profile(_,_).

% = Preference_Relation.thy
% Preference_Relation.connex_imp_refl
refl_on(A,R) :- connex(A,R).

% = Result_Facts.thy
% Result_Facts.drop_two_mod_rej_two
rejects(2,drop_module(2,R)) :- linear_order(R).

% = Result_Facts.thy
% Result_Facts.drop_zero_mod_rej_zero
rejects(0,drop_module(0,R)) :- linear_order(R).

% = Sequential_Composition.thy
% Sequential_Composition.seq_comp_presv_alts
set_equals_partition(A,sequential_composition(M,N,A,P)) :- electoral_module(M),electoral_module(N),finite_profile(A,P).

% = generated
% trans_intro
trans(_).

% = Preference_Relation.thy
% Preference_Relation.lin_imp_trans
trans(R) :- linear_order_on(A,R).

% = generated
% wins_intro
wins(_,_,_).

