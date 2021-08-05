% ==== ../virage/src/test/resources/old_theories/ - Verified_Voting_Rule_Construction
%
% === component_type
% == nat
% == set
% == alternative
% == Preference_Relation
% == Profile
% == Result
% == Aggregator
% max_aggregator
% == Evaluation_Function
% == Termination_Condition
% defer_equal_condition(nat)
%
% === composable_module - Electoral_Module
% defer_module
% drop_module(nat, Preference_Relation)
% elect_module
% pass_module(nat, Preference_Relation)
% plurality
%
% === compositional_structure
% parallel_composition(Electoral_Module, Electoral_Module, Aggregator)
% revision_composition(Electoral_Module)
% sequential_composition(Electoral_Module)
% loop_composition(Electoral_Module, Termination_Condition)
% iter(Electoral_Module)
%
% === property
%% defer(Electoral_Module, set, Profile, alternative)
% defers(nat, Electoral_Module)
% rejects(nat, Electoral_Module)
% eliminates(nat, Electoral_Module)
% elects(nat, Electoral_Module)
% non_blocking(Electoral_Module)
% electing(Electoral_Module)
% non_electing(Electoral_Module)
%% defer_deciding(Electoral_Module)
%% decrementing(Electoral_Module)
%% defer_condorcet_consistency(Electoral_Module)
%% condorcet_compatibility(Electoral_Module)
% defer_monotonicity(Electoral_Module)
% defer_lift_invariance(Electoral_Module)
% disjoint_compatibility(Electoral_Module, Electoral_Module)
% invariant_monotonicity(Electoral_Module)
% defer_invariant_monotonicity(Electoral_Module)
% condorcet_winner(set, Profile, alternative)
% profile(set, Profile)
% finite_profile(set, Profile)
%% condorcet_consistency(Electoral_Module)
% monotonicity(Electoral_Module)
%% homogeneity(Electoral_Module)
%
% === composition_rule
% = Maximum_Aggregator.thy
% max_agg_consv
agg_conservative(max_aggregator).
% 
% = Maximum_Aggregator.thy
% max_agg_comm
agg_commutative(max_aggregator).
%
%% = Electoral_Module.thy
%% ccomp_and_dd_imp_def_only_winner
%% defer(M,A,P,W) :- condorcet_compatibility(M), defer_deciding(M), condorcet_winner(A,P,W).
%
%% = Electoral_Module.thy
%% ccomp_and_dd_imp_dcc
%% defer_condorcet_consistency(M) :- condorcet_compatibility(M), defer_deciding(M).
%
% = Sequential_Composition.thy
% disj_comp_seq
disjoint_compatibility(sequential_composition(M, _), N) :- disjoint_compatibility(M,N).
% = Drop_And_Pass_Compatibility
% drop_pass_disj_compat
disjoint_compatibility(drop_module(N,R), pass_module(N,R)).
% = Electoral_Module.thy
% disj_compat_comm
disjoint_compatibility(N,M) :- disjoint_compatibility(M,N).
%
% = Electoral_Module.thy
% dl_inv_imp_def_mono
defer_monotonicity(M) :- defer_lift_invariance(M).
%
% = Defer_Module.thy
% def_mod_non_electing
non_electing(defer_module).
% = Drop_Module.thy
% drop_mod_non_electing
non_electing(drop_module(_,_)).
% = Pass_Module.thy
% pass_mod_non_electing
non_electing(pass_module(_,_)).
% = Revision_Composition.thy
% rev_comp_non_electing
non_electing(revision_composition(_)).
% = Parallel_Composition.thy
% conserv_agg_presv_non_electing
non_electing(parallel_composition(M,N,A)) :- non_electing(M), non_electing(N), agg_conservative(A).
% = Maximum_Parallel_Composition.thy
% conserv_max_agg_presv_non_electing
non_electing(parallel_composition(M,N,max_aggregator)) :- non_electing(M), non_electing(N).
% = Sequential_Composition.thy
% seq_comp_presv_non_electing
non_electing(sequential_composition(M,N)) :- non_electing(M), non_electing(N).
% = Loop_Composition.thy
% loop_comp_presv_non_electing
non_electing(loop_composition(M,_)) :- non_electing(M).
%
% = Defer_Module.thy
% def_mod_def_lift_invariant
defer_lift_invariance(defer_module).
% = Drop_Module.thy
% drop_mod_def_lift_invariant
defer_lift_invariance(drop_module(_,_)).
% = Pass_Module.thy
% pass_mod_dl_inv
defer_lift_invariance(pass_module(_,_)).
% = Maximum_Parallel_Composition.thy
% par_comp_def_lift_inv
defer_lift_invariance(parallel_composition(M,N,max_aggregator)) :- disjoint_compatibility(M,N), defer_lift_invariance(M), defer_lift_invariance(N).
% = Sequential_Composition.thy
% seq_comp_presv_def_lift_inv
defer_lift_invariance(sequential_composition(M,N)) :- defer_lift_invariance(M), defer_lift_invariance(N).
% = Sequential_Composition.thy
% def_inv_mono_imp_def_lift_inv
defer_lift_invariance(sequential_composition(M,N)) :- defer_invariant_monotonicity(M), non_electing(N), defers(1,N), defer_monotonicity(N).
% = Loop_Composition.thy
% loop_comp_presv_def_lift_inv
defer_lift_invariance(loop_composition(M,_)) :- defer_lift_invariance(M).
%
% = Elect_Module.thy
% elect_mod_electing
electing(elect_module).
% = Plurality_Module.thy
% plurality_electing
electing(plurality).
% = Sequential_Composition.thy
% seq_comp_electing
electing(sequential_composition(M,N)) :- defers(1,M), electing(N).
% = Elect_Composition.thy
% elector_electing
electing(sequential_composition(M,elect_module)) :- non_blocking(M).
%
% = Pass_Module.thy
% pass_mod_non_blocking
non_blocking(pass_module(_,_)).
% = Revision_Composition.thy
% rev_comp_non_blocking
non_blocking(revision_composition(M)) :- electing(M).
%
% = Pass_Module.thy
% pass_one_mod_def_one
defers(1, pass_module(1,_)).
% = Pass_Module.thy
% pass_two_mod_def_two
defers(2, pass_module(2,_)).
% = Sequential_Composition.thy
% seq_comp_def_one
defers(1, sequential_composition(M,N)) :- non_blocking(M), non_electing(M), defers(1,N).
% = Loop_Composition.thy
% iter_elim_def_n
defers(1,loop_composition(M,defer_equal_condition(1))) :- non_electing(M), eliminates(1,M).
%
% = Drop_And_Pass_Compatibility
% drop_two_mod_rej_two
rejects(2, drop_module(2,_)).
%
% = Plurality_Module.thy
% plurality_inv_mono
invariant_monotonicity(plurality).
%
% = Maximum_Parallel_Composition.thy
% par_comp_elim_one
eliminates(1, parallel_composition(M,N,max_aggregator)) :- defers(1,M), non_electing(M), rejects(2,N), disjoint_compatibility(M,N).
%
% = Revision_Composition.thy
% rev_comp_def_inv_mono
defer_invariant_monotonicity(revision_composition(M)) :- invariant_monotonicity(M).
%
% = Sequential_Composition.thy
% seq_comp_mono
monotonicity(sequential_composition(M,N)) :- defer_lift_invariance(M), non_electing(M), defers(1,M), electing(N).
%
%% = Elect_Composition.thy
%% dcc_imp_cc_elector
%% condorcet_consistency(sequential_composition(M,elect_module)) :- defer_condorcet_consistency(M).