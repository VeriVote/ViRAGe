% ==== ./VerifiedVotingRuleConstruction/theories/ - Verified_Voting_Rule_Construction
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
% pairwise_majority_rule()
% minimax()
% elect_module()
% defer_module()
% drop_module(Nat.nat,Preference_Relation)
% elimination_module(Evaluation_Function,Nat.nat,Nat.nat,Nat.nat,HOL.bool)
% pairwise_majority_rule'()
% minimax_rule()
% borda()
% pass_module(Nat.nat,Preference_Relation)
% smc(Preference_Relation)
% nanson_baldwin_rule()
% copeland_rule()
% less_average_eliminator(Evaluation_Function)
% max_eliminator(Evaluation_Function)
% leq_eliminator(Evaluation_Function,Nat.nat)
% condorcet'()
% copeland()
% blacks_rule()
% condorcet()
% less_eliminator(Evaluation_Function,Nat.nat)
% plurality()
% borda_rule()
% leq_average_eliminator(Evaluation_Function)
% classic_nanson_rule()
% schwartz_rule()
% min_eliminator(Evaluation_Function)
% == Nat.nat
% win_count_code(Profile,?'a)
% average(Evaluation_Function,Set.set(?'a),Profile)
% prefer_count_code(Profile,?'a,?'a)
% win_count(Profile,?'a)
% rank(Preference_Relation,?'a)
% prefer_count(Profile,?'a,?'a)
% == Termination_Condition
% set_equals_partition(Set.set(?'a))
% defer_equal_condition(Nat.nat)
% disjoint3()
% well_formed(Set.set(?'a))
% == ?'a
% == Evaluation_Function
% borda_score()
% condorcet_score()
% minimax_score()
% copeland_score()
%
% === composable_module
%% This area is deprecated and therefore intentionally empty.
% === compositional_structure
% iterelect(Electoral_Module)
% iter(Electoral_Module)
% loop_comp_helper(Electoral_Module,Electoral_Module,Termination_Condition)
% limit(Set.set(?'a),Preference_Relation)
% loop_composition(Electoral_Module,Termination_Condition)
% sequential_composition(Electoral_Module,Electoral_Module)
% times(Nat.nat,List.list(?'a))
% revision_composition(Electoral_Module)
% maximum_parallel_composition(Electoral_Module,Electoral_Module)
% elector(Electoral_Module)
% elimination_set(Evaluation_Function,Nat.nat,Nat.nat,Nat.nat,HOL.bool,Set.set(?'a),Profile)
% limit_profile(Set.set(?'a),Profile)
% parallel_composition(Electoral_Module,Electoral_Module,Aggregator)
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

% = generated
% equiv_prof_except_a_intro
equiv_prof_except_a(_,_,_,_).

% = generated
% equiv_rel_except_a_intro
equiv_rel_except_a(_,_,_,_).

% = generated
% finite_profile_intro
finite_profile(_,_).

% = generated
% is_less_preferred_than_intro
is_less_preferred_than(_,_,_).

% = generated
% lifted_intro
lifted(_,_,_,_).

% = generated
% limited_intro
limited(_,_).

% = generated
% linear_order_intro
linear_order(_).

% = generated
% profile_intro
profile(_,_).

% = generated
% trans_intro
trans(_).

% = generated
% wins_intro
wins(_,_,_).

