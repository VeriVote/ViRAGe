%%%%%%%%%%%%%%%%%%%%
%% Generated by ViRAGe 0.1.0 at 2021-08-26 17:45:20 CEST.
%%%%%%%%%%%%%%%%%%%%
%% To add new composition rules, go to the bottom of this file.
%% A rule definition consists of three parts. The first one represents its origin,
%% for user defined rules this will always be "UNPROVEN". The second part is
%% the symbolic name of the rule that will be used in generated proofs.
%% The third part is a Prolog clause capturing the semantics of the rule.
%%
%% Example:
%% % = UNPROVEN
%% % example_rule_without_meaning
%% property_a(X) :- property_b(X).
%%%%%%%%%%%%%%%%%%%%
% ==== ../virage/src/test/resources/old_theories/ROOT - Verified_Voting_Rule_Construction
%
% === COMPONENT_TYPE
% == set
% == nat
% == Set.set(?'a)
% == Aggregator
% max_aggregator()
% == alternative
% == List.list(?'a)
% == Preference_Relation
% == Result
% == Profile
% == Rel.rel(?'a)
% == Electoral_Module
% == HOL.bool
% == Termination_Condition
% defer_equal_condition(nat)
% == ?'a
% == Evaluation_Function
%
% === PROPERTY
% defers(nat,Electoral_Module)
% profile(set,Profile)
% electing(Electoral_Module)
% non_electing(Electoral_Module)
% defer_invariant_monotonicity(Electoral_Module)
% defer_lift_invariance(Electoral_Module)
% monotonicity(Electoral_Module)
% non_blocking(Electoral_Module)
% eliminates(nat,Electoral_Module)
% defer_monotonicity(Electoral_Module)
% rejects(nat,Electoral_Module)
% disjoint_compatibility(Electoral_Module,Electoral_Module)
% elects(nat,Electoral_Module)
% invariant_monotonicity(Electoral_Module)
% finite_profile(set,Profile)
% condorcet_winner(set,Profile,alternative)
% linear_order(Preference_Relation)
% trans(Preference_Relation)
% finite_profile(Set.set(?'a),Profile)
%
% === COMPOSITION_RULE
% = Maximum_Aggregator.thy
% max_agg_comm
agg_commutative(max_aggregator).

% = Maximum_Aggregator.thy
% max_agg_consv
agg_conservative(max_aggregator).

% = ASSUMPTION
% condorcet_winner_alias_0
condorcet_winner(iter(X),ALIAS_VAR_1,ALIAS_VAR_2) :- condorcet_winner(loop_composition(X,defer_equal_condition(1)),ALIAS_VAR_1,ALIAS_VAR_2).

% = ASSUMPTION
% condorcet_winner_alias_1
condorcet_winner(iterelect(X),ALIAS_VAR_1,ALIAS_VAR_2) :- condorcet_winner(elector(iter(X)),ALIAS_VAR_1,ALIAS_VAR_2).

% = ASSUMPTION
% condorcet_winner_alias_2
condorcet_winner(maximum_parallel_composition(X,Y),ALIAS_VAR_1,ALIAS_VAR_2) :- condorcet_winner(parallel_composition(X,Y,max_aggregator),ALIAS_VAR_1,ALIAS_VAR_2).

% = ASSUMPTION
% condorcet_winner_alias_3
condorcet_winner(smc(X),ALIAS_VAR_1,ALIAS_VAR_2) :- condorcet_winner(iterelect(maximum_parallel_composition(sequential_composition(pass_module(2,X),sequential_composition(revision_composition(plurality),pass_module(1,X))),drop_module(2,X))),ALIAS_VAR_1,ALIAS_VAR_2).

% = ASSUMPTION
% condorcet_winner_alias_4
condorcet_winner(elector(X),ALIAS_VAR_1,ALIAS_VAR_2) :- condorcet_winner(sequential_composition(X,elect_module),ALIAS_VAR_1,ALIAS_VAR_2).

% = ASSUMPTION
% condorcet_winner_alias_0
condorcet_winner(ALIAS_VAR_0,iter(X),ALIAS_VAR_2) :- condorcet_winner(ALIAS_VAR_0,loop_composition(X,defer_equal_condition(1)),ALIAS_VAR_2).

% = ASSUMPTION
% condorcet_winner_alias_1
condorcet_winner(ALIAS_VAR_0,iterelect(X),ALIAS_VAR_2) :- condorcet_winner(ALIAS_VAR_0,elector(iter(X)),ALIAS_VAR_2).

% = ASSUMPTION
% condorcet_winner_alias_2
condorcet_winner(ALIAS_VAR_0,maximum_parallel_composition(X,Y),ALIAS_VAR_2) :- condorcet_winner(ALIAS_VAR_0,parallel_composition(X,Y,max_aggregator),ALIAS_VAR_2).

% = ASSUMPTION
% condorcet_winner_alias_3
condorcet_winner(ALIAS_VAR_0,smc(X),ALIAS_VAR_2) :- condorcet_winner(ALIAS_VAR_0,iterelect(maximum_parallel_composition(sequential_composition(pass_module(2,X),sequential_composition(revision_composition(plurality),pass_module(1,X))),drop_module(2,X))),ALIAS_VAR_2).

% = ASSUMPTION
% condorcet_winner_alias_4
condorcet_winner(ALIAS_VAR_0,elector(X),ALIAS_VAR_2) :- condorcet_winner(ALIAS_VAR_0,sequential_composition(X,elect_module),ALIAS_VAR_2).

% = ASSUMPTION
% condorcet_winner_alias_0
condorcet_winner(ALIAS_VAR_0,ALIAS_VAR_1,iter(X)) :- condorcet_winner(ALIAS_VAR_0,ALIAS_VAR_1,loop_composition(X,defer_equal_condition(1))).

% = ASSUMPTION
% condorcet_winner_alias_1
condorcet_winner(ALIAS_VAR_0,ALIAS_VAR_1,iterelect(X)) :- condorcet_winner(ALIAS_VAR_0,ALIAS_VAR_1,elector(iter(X))).

% = ASSUMPTION
% condorcet_winner_alias_2
condorcet_winner(ALIAS_VAR_0,ALIAS_VAR_1,maximum_parallel_composition(X,Y)) :- condorcet_winner(ALIAS_VAR_0,ALIAS_VAR_1,parallel_composition(X,Y,max_aggregator)).

% = ASSUMPTION
% condorcet_winner_alias_3
condorcet_winner(ALIAS_VAR_0,ALIAS_VAR_1,smc(X)) :- condorcet_winner(ALIAS_VAR_0,ALIAS_VAR_1,iterelect(maximum_parallel_composition(sequential_composition(pass_module(2,X),sequential_composition(revision_composition(plurality),pass_module(1,X))),drop_module(2,X)))).

% = ASSUMPTION
% condorcet_winner_alias_4
condorcet_winner(ALIAS_VAR_0,ALIAS_VAR_1,elector(X)) :- condorcet_winner(ALIAS_VAR_0,ALIAS_VAR_1,sequential_composition(X,elect_module)).

% = Revision_Composition.thy
% rev_comp_def_inv_mono
defer_invariant_monotonicity(revision_composition(M)) :- invariant_monotonicity(M).

% = ASSUMPTION
% defer_invariant_monotonicity_alias_0
defer_invariant_monotonicity(iter(X)) :- defer_invariant_monotonicity(loop_composition(X,defer_equal_condition(1))).

% = ASSUMPTION
% defer_invariant_monotonicity_alias_1
defer_invariant_monotonicity(iterelect(X)) :- defer_invariant_monotonicity(elector(iter(X))).

% = ASSUMPTION
% defer_invariant_monotonicity_alias_2
defer_invariant_monotonicity(maximum_parallel_composition(X,Y)) :- defer_invariant_monotonicity(parallel_composition(X,Y,max_aggregator)).

% = ASSUMPTION
% defer_invariant_monotonicity_alias_3
defer_invariant_monotonicity(smc(X)) :- defer_invariant_monotonicity(iterelect(maximum_parallel_composition(sequential_composition(pass_module(2,X),sequential_composition(revision_composition(plurality),pass_module(1,X))),drop_module(2,X)))).

% = ASSUMPTION
% defer_invariant_monotonicity_alias_4
defer_invariant_monotonicity(elector(X)) :- defer_invariant_monotonicity(sequential_composition(X,elect_module)).

% = Defer_Module.thy
% def_mod_def_lift_invariant
defer_lift_invariance(defer_module).

% = Drop_Module.thy
% drop_mod_def_lift_invariant
defer_lift_invariance(drop_module(_,_)).

% = Pass_Module.thy
% pass_mod_dl_inv
defer_lift_invariance(pass_module(_,_)).

% = Loop_Composition.thy
% loop_comp_presv_def_lift_inv
defer_lift_invariance(loop_composition(M,_)) :- defer_lift_invariance(M).

% = ASSUMPTION
% defer_lift_invariance_alias_0
defer_lift_invariance(iter(X)) :- defer_lift_invariance(loop_composition(X,defer_equal_condition(1))).

% = ASSUMPTION
% defer_lift_invariance_alias_1
defer_lift_invariance(iterelect(X)) :- defer_lift_invariance(elector(iter(X))).

% = ASSUMPTION
% defer_lift_invariance_alias_2
defer_lift_invariance(maximum_parallel_composition(X,Y)) :- defer_lift_invariance(parallel_composition(X,Y,max_aggregator)).

% = ASSUMPTION
% defer_lift_invariance_alias_3
defer_lift_invariance(smc(X)) :- defer_lift_invariance(iterelect(maximum_parallel_composition(sequential_composition(pass_module(2,X),sequential_composition(revision_composition(plurality),pass_module(1,X))),drop_module(2,X)))).

% = ASSUMPTION
% defer_lift_invariance_alias_4
defer_lift_invariance(elector(X)) :- defer_lift_invariance(sequential_composition(X,elect_module)).

% = Sequential_Composition.thy
% seq_comp_presv_def_lift_inv
defer_lift_invariance(sequential_composition(M,N)) :- defer_lift_invariance(M),defer_lift_invariance(N).

% = Maximum_Parallel_Composition.thy
% par_comp_def_lift_inv
defer_lift_invariance(parallel_composition(M,N,max_aggregator)) :- disjoint_compatibility(M,N),defer_lift_invariance(M),defer_lift_invariance(N).

% = Sequential_Composition.thy
% def_inv_mono_imp_def_lift_inv
defer_lift_invariance(sequential_composition(M,N)) :- defer_invariant_monotonicity(M),non_electing(N),defers(1,N),defer_monotonicity(N).

% = Electoral_Module.thy
% dl_inv_imp_def_mono
defer_monotonicity(M) :- defer_lift_invariance(M).

% = ASSUMPTION
% defer_monotonicity_alias_0
defer_monotonicity(iter(X)) :- defer_monotonicity(loop_composition(X,defer_equal_condition(1))).

% = ASSUMPTION
% defer_monotonicity_alias_1
defer_monotonicity(iterelect(X)) :- defer_monotonicity(elector(iter(X))).

% = ASSUMPTION
% defer_monotonicity_alias_2
defer_monotonicity(maximum_parallel_composition(X,Y)) :- defer_monotonicity(parallel_composition(X,Y,max_aggregator)).

% = ASSUMPTION
% defer_monotonicity_alias_3
defer_monotonicity(smc(X)) :- defer_monotonicity(iterelect(maximum_parallel_composition(sequential_composition(pass_module(2,X),sequential_composition(revision_composition(plurality),pass_module(1,X))),drop_module(2,X)))).

% = ASSUMPTION
% defer_monotonicity_alias_4
defer_monotonicity(elector(X)) :- defer_monotonicity(sequential_composition(X,elect_module)).

% = Pass_Module.thy
% pass_one_mod_def_one
defers(1,pass_module(1,_)).

% = Pass_Module.thy
% pass_two_mod_def_two
defers(2,pass_module(2,_)).

% = ASSUMPTION
% defers_alias_0
defers(iter(X),ALIAS_VAR_1) :- defers(loop_composition(X,defer_equal_condition(1)),ALIAS_VAR_1).

% = ASSUMPTION
% defers_alias_1
defers(iterelect(X),ALIAS_VAR_1) :- defers(elector(iter(X)),ALIAS_VAR_1).

% = ASSUMPTION
% defers_alias_2
defers(maximum_parallel_composition(X,Y),ALIAS_VAR_1) :- defers(parallel_composition(X,Y,max_aggregator),ALIAS_VAR_1).

% = ASSUMPTION
% defers_alias_3
defers(smc(X),ALIAS_VAR_1) :- defers(iterelect(maximum_parallel_composition(sequential_composition(pass_module(2,X),sequential_composition(revision_composition(plurality),pass_module(1,X))),drop_module(2,X))),ALIAS_VAR_1).

% = ASSUMPTION
% defers_alias_4
defers(elector(X),ALIAS_VAR_1) :- defers(sequential_composition(X,elect_module),ALIAS_VAR_1).

% = ASSUMPTION
% defers_alias_0
defers(ALIAS_VAR_0,iter(X)) :- defers(ALIAS_VAR_0,loop_composition(X,defer_equal_condition(1))).

% = ASSUMPTION
% defers_alias_1
defers(ALIAS_VAR_0,iterelect(X)) :- defers(ALIAS_VAR_0,elector(iter(X))).

% = ASSUMPTION
% defers_alias_2
defers(ALIAS_VAR_0,maximum_parallel_composition(X,Y)) :- defers(ALIAS_VAR_0,parallel_composition(X,Y,max_aggregator)).

% = ASSUMPTION
% defers_alias_3
defers(ALIAS_VAR_0,smc(X)) :- defers(ALIAS_VAR_0,iterelect(maximum_parallel_composition(sequential_composition(pass_module(2,X),sequential_composition(revision_composition(plurality),pass_module(1,X))),drop_module(2,X)))).

% = ASSUMPTION
% defers_alias_4
defers(ALIAS_VAR_0,elector(X)) :- defers(ALIAS_VAR_0,sequential_composition(X,elect_module)).

% = Loop_Composition.thy
% iter_elim_def_n
defers(1,loop_composition(M,defer_equal_condition(1))) :- non_electing(M),eliminates(1,M).

% = Sequential_Composition.thy
% seq_comp_def_one
defers(1,sequential_composition(M,N)) :- non_blocking(M),non_electing(M),defers(1,N).

% = Drop_And_Pass_Compatibility
% drop_pass_disj_compat
disjoint_compatibility(drop_module(N,R),pass_module(N,R)).

% = Sequential_Composition.thy
% disj_comp_seq
disjoint_compatibility(sequential_composition(M,_),N) :- disjoint_compatibility(M,N).

% = Electoral_Module.thy
% disj_compat_comm
disjoint_compatibility(N,M) :- disjoint_compatibility(M,N).

% = ASSUMPTION
% disjoint_compatibility_alias_0
disjoint_compatibility(iter(X),ALIAS_VAR_1) :- disjoint_compatibility(loop_composition(X,defer_equal_condition(1)),ALIAS_VAR_1).

% = ASSUMPTION
% disjoint_compatibility_alias_1
disjoint_compatibility(iterelect(X),ALIAS_VAR_1) :- disjoint_compatibility(elector(iter(X)),ALIAS_VAR_1).

% = ASSUMPTION
% disjoint_compatibility_alias_2
disjoint_compatibility(maximum_parallel_composition(X,Y),ALIAS_VAR_1) :- disjoint_compatibility(parallel_composition(X,Y,max_aggregator),ALIAS_VAR_1).

% = ASSUMPTION
% disjoint_compatibility_alias_3
disjoint_compatibility(smc(X),ALIAS_VAR_1) :- disjoint_compatibility(iterelect(maximum_parallel_composition(sequential_composition(pass_module(2,X),sequential_composition(revision_composition(plurality),pass_module(1,X))),drop_module(2,X))),ALIAS_VAR_1).

% = ASSUMPTION
% disjoint_compatibility_alias_4
disjoint_compatibility(elector(X),ALIAS_VAR_1) :- disjoint_compatibility(sequential_composition(X,elect_module),ALIAS_VAR_1).

% = ASSUMPTION
% disjoint_compatibility_alias_0
disjoint_compatibility(ALIAS_VAR_0,iter(X)) :- disjoint_compatibility(ALIAS_VAR_0,loop_composition(X,defer_equal_condition(1))).

% = ASSUMPTION
% disjoint_compatibility_alias_1
disjoint_compatibility(ALIAS_VAR_0,iterelect(X)) :- disjoint_compatibility(ALIAS_VAR_0,elector(iter(X))).

% = ASSUMPTION
% disjoint_compatibility_alias_2
disjoint_compatibility(ALIAS_VAR_0,maximum_parallel_composition(X,Y)) :- disjoint_compatibility(ALIAS_VAR_0,parallel_composition(X,Y,max_aggregator)).

% = ASSUMPTION
% disjoint_compatibility_alias_3
disjoint_compatibility(ALIAS_VAR_0,smc(X)) :- disjoint_compatibility(ALIAS_VAR_0,iterelect(maximum_parallel_composition(sequential_composition(pass_module(2,X),sequential_composition(revision_composition(plurality),pass_module(1,X))),drop_module(2,X)))).

% = ASSUMPTION
% disjoint_compatibility_alias_4
disjoint_compatibility(ALIAS_VAR_0,elector(X)) :- disjoint_compatibility(ALIAS_VAR_0,sequential_composition(X,elect_module)).

% = Elect_Module.thy
% elect_mod_electing
electing(elect_module).

% = Plurality_Module.thy
% plurality_electing
electing(plurality).

% = Elect_Composition.thy
% elector_electing
electing(sequential_composition(M,elect_module)) :- non_blocking(M).

% = ASSUMPTION
% electing_alias_0
electing(iter(X)) :- electing(loop_composition(X,defer_equal_condition(1))).

% = ASSUMPTION
% electing_alias_1
electing(iterelect(X)) :- electing(elector(iter(X))).

% = ASSUMPTION
% electing_alias_2
electing(maximum_parallel_composition(X,Y)) :- electing(parallel_composition(X,Y,max_aggregator)).

% = ASSUMPTION
% electing_alias_3
electing(smc(X)) :- electing(iterelect(maximum_parallel_composition(sequential_composition(pass_module(2,X),sequential_composition(revision_composition(plurality),pass_module(1,X))),drop_module(2,X)))).

% = ASSUMPTION
% electing_alias_4
electing(elector(X)) :- electing(sequential_composition(X,elect_module)).

% = Sequential_Composition.thy
% seq_comp_electing
electing(sequential_composition(M,N)) :- defers(1,M),electing(N).

% = ASSUMPTION
% elects_alias_0
elects(iter(X),ALIAS_VAR_1) :- elects(loop_composition(X,defer_equal_condition(1)),ALIAS_VAR_1).

% = ASSUMPTION
% elects_alias_1
elects(iterelect(X),ALIAS_VAR_1) :- elects(elector(iter(X)),ALIAS_VAR_1).

% = ASSUMPTION
% elects_alias_2
elects(maximum_parallel_composition(X,Y),ALIAS_VAR_1) :- elects(parallel_composition(X,Y,max_aggregator),ALIAS_VAR_1).

% = ASSUMPTION
% elects_alias_3
elects(smc(X),ALIAS_VAR_1) :- elects(iterelect(maximum_parallel_composition(sequential_composition(pass_module(2,X),sequential_composition(revision_composition(plurality),pass_module(1,X))),drop_module(2,X))),ALIAS_VAR_1).

% = ASSUMPTION
% elects_alias_4
elects(elector(X),ALIAS_VAR_1) :- elects(sequential_composition(X,elect_module),ALIAS_VAR_1).

% = ASSUMPTION
% elects_alias_0
elects(ALIAS_VAR_0,iter(X)) :- elects(ALIAS_VAR_0,loop_composition(X,defer_equal_condition(1))).

% = ASSUMPTION
% elects_alias_1
elects(ALIAS_VAR_0,iterelect(X)) :- elects(ALIAS_VAR_0,elector(iter(X))).

% = ASSUMPTION
% elects_alias_2
elects(ALIAS_VAR_0,maximum_parallel_composition(X,Y)) :- elects(ALIAS_VAR_0,parallel_composition(X,Y,max_aggregator)).

% = ASSUMPTION
% elects_alias_3
elects(ALIAS_VAR_0,smc(X)) :- elects(ALIAS_VAR_0,iterelect(maximum_parallel_composition(sequential_composition(pass_module(2,X),sequential_composition(revision_composition(plurality),pass_module(1,X))),drop_module(2,X)))).

% = ASSUMPTION
% elects_alias_4
elects(ALIAS_VAR_0,elector(X)) :- elects(ALIAS_VAR_0,sequential_composition(X,elect_module)).

% = ASSUMPTION
% eliminates_alias_0
eliminates(iter(X),ALIAS_VAR_1) :- eliminates(loop_composition(X,defer_equal_condition(1)),ALIAS_VAR_1).

% = ASSUMPTION
% eliminates_alias_1
eliminates(iterelect(X),ALIAS_VAR_1) :- eliminates(elector(iter(X)),ALIAS_VAR_1).

% = ASSUMPTION
% eliminates_alias_2
eliminates(maximum_parallel_composition(X,Y),ALIAS_VAR_1) :- eliminates(parallel_composition(X,Y,max_aggregator),ALIAS_VAR_1).

% = ASSUMPTION
% eliminates_alias_3
eliminates(smc(X),ALIAS_VAR_1) :- eliminates(iterelect(maximum_parallel_composition(sequential_composition(pass_module(2,X),sequential_composition(revision_composition(plurality),pass_module(1,X))),drop_module(2,X))),ALIAS_VAR_1).

% = ASSUMPTION
% eliminates_alias_4
eliminates(elector(X),ALIAS_VAR_1) :- eliminates(sequential_composition(X,elect_module),ALIAS_VAR_1).

% = ASSUMPTION
% eliminates_alias_0
eliminates(ALIAS_VAR_0,iter(X)) :- eliminates(ALIAS_VAR_0,loop_composition(X,defer_equal_condition(1))).

% = ASSUMPTION
% eliminates_alias_1
eliminates(ALIAS_VAR_0,iterelect(X)) :- eliminates(ALIAS_VAR_0,elector(iter(X))).

% = ASSUMPTION
% eliminates_alias_2
eliminates(ALIAS_VAR_0,maximum_parallel_composition(X,Y)) :- eliminates(ALIAS_VAR_0,parallel_composition(X,Y,max_aggregator)).

% = ASSUMPTION
% eliminates_alias_3
eliminates(ALIAS_VAR_0,smc(X)) :- eliminates(ALIAS_VAR_0,iterelect(maximum_parallel_composition(sequential_composition(pass_module(2,X),sequential_composition(revision_composition(plurality),pass_module(1,X))),drop_module(2,X)))).

% = ASSUMPTION
% eliminates_alias_4
eliminates(ALIAS_VAR_0,elector(X)) :- eliminates(ALIAS_VAR_0,sequential_composition(X,elect_module)).

% = Maximum_Parallel_Composition.thy
% par_comp_elim_one
eliminates(1,parallel_composition(M,N,max_aggregator)) :- defers(1,M),non_electing(M),rejects(2,N),disjoint_compatibility(M,N).

% = ASSUMPTION
% finite_profile_alias_0
finite_profile(iter(X),ALIAS_VAR_1) :- finite_profile(loop_composition(X,defer_equal_condition(1)),ALIAS_VAR_1).

% = ASSUMPTION
% finite_profile_alias_1
finite_profile(iterelect(X),ALIAS_VAR_1) :- finite_profile(elector(iter(X)),ALIAS_VAR_1).

% = ASSUMPTION
% finite_profile_alias_2
finite_profile(maximum_parallel_composition(X,Y),ALIAS_VAR_1) :- finite_profile(parallel_composition(X,Y,max_aggregator),ALIAS_VAR_1).

% = ASSUMPTION
% finite_profile_alias_3
finite_profile(smc(X),ALIAS_VAR_1) :- finite_profile(iterelect(maximum_parallel_composition(sequential_composition(pass_module(2,X),sequential_composition(revision_composition(plurality),pass_module(1,X))),drop_module(2,X))),ALIAS_VAR_1).

% = ASSUMPTION
% finite_profile_alias_4
finite_profile(elector(X),ALIAS_VAR_1) :- finite_profile(sequential_composition(X,elect_module),ALIAS_VAR_1).

% = ASSUMPTION
% finite_profile_alias_0
finite_profile(ALIAS_VAR_0,iter(X)) :- finite_profile(ALIAS_VAR_0,loop_composition(X,defer_equal_condition(1))).

% = ASSUMPTION
% finite_profile_alias_1
finite_profile(ALIAS_VAR_0,iterelect(X)) :- finite_profile(ALIAS_VAR_0,elector(iter(X))).

% = ASSUMPTION
% finite_profile_alias_2
finite_profile(ALIAS_VAR_0,maximum_parallel_composition(X,Y)) :- finite_profile(ALIAS_VAR_0,parallel_composition(X,Y,max_aggregator)).

% = ASSUMPTION
% finite_profile_alias_3
finite_profile(ALIAS_VAR_0,smc(X)) :- finite_profile(ALIAS_VAR_0,iterelect(maximum_parallel_composition(sequential_composition(pass_module(2,X),sequential_composition(revision_composition(plurality),pass_module(1,X))),drop_module(2,X)))).

% = ASSUMPTION
% finite_profile_alias_4
finite_profile(ALIAS_VAR_0,elector(X)) :- finite_profile(ALIAS_VAR_0,sequential_composition(X,elect_module)).

% = Plurality_Module.thy
% plurality_inv_mono
invariant_monotonicity(plurality).

% = ASSUMPTION
% invariant_monotonicity_alias_0
invariant_monotonicity(iter(X)) :- invariant_monotonicity(loop_composition(X,defer_equal_condition(1))).

% = ASSUMPTION
% invariant_monotonicity_alias_1
invariant_monotonicity(iterelect(X)) :- invariant_monotonicity(elector(iter(X))).

% = ASSUMPTION
% invariant_monotonicity_alias_2
invariant_monotonicity(maximum_parallel_composition(X,Y)) :- invariant_monotonicity(parallel_composition(X,Y,max_aggregator)).

% = ASSUMPTION
% invariant_monotonicity_alias_3
invariant_monotonicity(smc(X)) :- invariant_monotonicity(iterelect(maximum_parallel_composition(sequential_composition(pass_module(2,X),sequential_composition(revision_composition(plurality),pass_module(1,X))),drop_module(2,X)))).

% = ASSUMPTION
% invariant_monotonicity_alias_4
invariant_monotonicity(elector(X)) :- invariant_monotonicity(sequential_composition(X,elect_module)).

% = ASSUMPTION
% monotonicity_alias_0
monotonicity(iter(X)) :- monotonicity(loop_composition(X,defer_equal_condition(1))).

% = ASSUMPTION
% monotonicity_alias_1
monotonicity(iterelect(X)) :- monotonicity(elector(iter(X))).

% = ASSUMPTION
% monotonicity_alias_2
monotonicity(maximum_parallel_composition(X,Y)) :- monotonicity(parallel_composition(X,Y,max_aggregator)).

% = ASSUMPTION
% monotonicity_alias_3
monotonicity(smc(X)) :- monotonicity(iterelect(maximum_parallel_composition(sequential_composition(pass_module(2,X),sequential_composition(revision_composition(plurality),pass_module(1,X))),drop_module(2,X)))).

% = ASSUMPTION
% monotonicity_alias_4
monotonicity(elector(X)) :- monotonicity(sequential_composition(X,elect_module)).

% = Sequential_Composition.thy
% seq_comp_mono
monotonicity(sequential_composition(M,N)) :- defer_lift_invariance(M),non_electing(M),defers(1,M),electing(N).

% = Pass_Module.thy
% pass_mod_non_blocking
non_blocking(pass_module(_,_)).

% = Revision_Composition.thy
% rev_comp_non_blocking
non_blocking(revision_composition(M)) :- electing(M).

% = ASSUMPTION
% non_blocking_alias_0
non_blocking(iter(X)) :- non_blocking(loop_composition(X,defer_equal_condition(1))).

% = ASSUMPTION
% non_blocking_alias_1
non_blocking(iterelect(X)) :- non_blocking(elector(iter(X))).

% = ASSUMPTION
% non_blocking_alias_2
non_blocking(maximum_parallel_composition(X,Y)) :- non_blocking(parallel_composition(X,Y,max_aggregator)).

% = ASSUMPTION
% non_blocking_alias_3
non_blocking(smc(X)) :- non_blocking(iterelect(maximum_parallel_composition(sequential_composition(pass_module(2,X),sequential_composition(revision_composition(plurality),pass_module(1,X))),drop_module(2,X)))).

% = ASSUMPTION
% non_blocking_alias_4
non_blocking(elector(X)) :- non_blocking(sequential_composition(X,elect_module)).

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

% = Loop_Composition.thy
% loop_comp_presv_non_electing
non_electing(loop_composition(M,_)) :- non_electing(M).

% = ASSUMPTION
% non_electing_alias_0
non_electing(iter(X)) :- non_electing(loop_composition(X,defer_equal_condition(1))).

% = ASSUMPTION
% non_electing_alias_1
non_electing(iterelect(X)) :- non_electing(elector(iter(X))).

% = ASSUMPTION
% non_electing_alias_2
non_electing(maximum_parallel_composition(X,Y)) :- non_electing(parallel_composition(X,Y,max_aggregator)).

% = ASSUMPTION
% non_electing_alias_3
non_electing(smc(X)) :- non_electing(iterelect(maximum_parallel_composition(sequential_composition(pass_module(2,X),sequential_composition(revision_composition(plurality),pass_module(1,X))),drop_module(2,X)))).

% = ASSUMPTION
% non_electing_alias_4
non_electing(elector(X)) :- non_electing(sequential_composition(X,elect_module)).

% = Maximum_Parallel_Composition.thy
% conserv_max_agg_presv_non_electing
non_electing(parallel_composition(M,N,max_aggregator)) :- non_electing(M),non_electing(N).

% = Sequential_Composition.thy
% seq_comp_presv_non_electing
non_electing(sequential_composition(M,N)) :- non_electing(M),non_electing(N).

% = Parallel_Composition.thy
% conserv_agg_presv_non_electing
non_electing(parallel_composition(M,N,A)) :- non_electing(M),non_electing(N),agg_conservative(A).

% = ASSUMPTION
% profile_alias_0
profile(iter(X),ALIAS_VAR_1) :- profile(loop_composition(X,defer_equal_condition(1)),ALIAS_VAR_1).

% = ASSUMPTION
% profile_alias_1
profile(iterelect(X),ALIAS_VAR_1) :- profile(elector(iter(X)),ALIAS_VAR_1).

% = ASSUMPTION
% profile_alias_2
profile(maximum_parallel_composition(X,Y),ALIAS_VAR_1) :- profile(parallel_composition(X,Y,max_aggregator),ALIAS_VAR_1).

% = ASSUMPTION
% profile_alias_3
profile(smc(X),ALIAS_VAR_1) :- profile(iterelect(maximum_parallel_composition(sequential_composition(pass_module(2,X),sequential_composition(revision_composition(plurality),pass_module(1,X))),drop_module(2,X))),ALIAS_VAR_1).

% = ASSUMPTION
% profile_alias_4
profile(elector(X),ALIAS_VAR_1) :- profile(sequential_composition(X,elect_module),ALIAS_VAR_1).

% = ASSUMPTION
% profile_alias_0
profile(ALIAS_VAR_0,iter(X)) :- profile(ALIAS_VAR_0,loop_composition(X,defer_equal_condition(1))).

% = ASSUMPTION
% profile_alias_1
profile(ALIAS_VAR_0,iterelect(X)) :- profile(ALIAS_VAR_0,elector(iter(X))).

% = ASSUMPTION
% profile_alias_2
profile(ALIAS_VAR_0,maximum_parallel_composition(X,Y)) :- profile(ALIAS_VAR_0,parallel_composition(X,Y,max_aggregator)).

% = ASSUMPTION
% profile_alias_3
profile(ALIAS_VAR_0,smc(X)) :- profile(ALIAS_VAR_0,iterelect(maximum_parallel_composition(sequential_composition(pass_module(2,X),sequential_composition(revision_composition(plurality),pass_module(1,X))),drop_module(2,X)))).

% = ASSUMPTION
% profile_alias_4
profile(ALIAS_VAR_0,elector(X)) :- profile(ALIAS_VAR_0,sequential_composition(X,elect_module)).

% = Drop_And_Pass_Compatibility
% drop_two_mod_rej_two
rejects(2,drop_module(2,_)).

% = ASSUMPTION
% rejects_alias_0
rejects(iter(X),ALIAS_VAR_1) :- rejects(loop_composition(X,defer_equal_condition(1)),ALIAS_VAR_1).

% = ASSUMPTION
% rejects_alias_1
rejects(iterelect(X),ALIAS_VAR_1) :- rejects(elector(iter(X)),ALIAS_VAR_1).

% = ASSUMPTION
% rejects_alias_2
rejects(maximum_parallel_composition(X,Y),ALIAS_VAR_1) :- rejects(parallel_composition(X,Y,max_aggregator),ALIAS_VAR_1).

% = ASSUMPTION
% rejects_alias_3
rejects(smc(X),ALIAS_VAR_1) :- rejects(iterelect(maximum_parallel_composition(sequential_composition(pass_module(2,X),sequential_composition(revision_composition(plurality),pass_module(1,X))),drop_module(2,X))),ALIAS_VAR_1).

% = ASSUMPTION
% rejects_alias_4
rejects(elector(X),ALIAS_VAR_1) :- rejects(sequential_composition(X,elect_module),ALIAS_VAR_1).

% = ASSUMPTION
% rejects_alias_0
rejects(ALIAS_VAR_0,iter(X)) :- rejects(ALIAS_VAR_0,loop_composition(X,defer_equal_condition(1))).

% = ASSUMPTION
% rejects_alias_1
rejects(ALIAS_VAR_0,iterelect(X)) :- rejects(ALIAS_VAR_0,elector(iter(X))).

% = ASSUMPTION
% rejects_alias_2
rejects(ALIAS_VAR_0,maximum_parallel_composition(X,Y)) :- rejects(ALIAS_VAR_0,parallel_composition(X,Y,max_aggregator)).

% = ASSUMPTION
% rejects_alias_3
rejects(ALIAS_VAR_0,smc(X)) :- rejects(ALIAS_VAR_0,iterelect(maximum_parallel_composition(sequential_composition(pass_module(2,X),sequential_composition(revision_composition(plurality),pass_module(1,X))),drop_module(2,X)))).

% = ASSUMPTION
% rejects_alias_4
rejects(ALIAS_VAR_0,elector(X)) :- rejects(ALIAS_VAR_0,sequential_composition(X,elect_module)).

