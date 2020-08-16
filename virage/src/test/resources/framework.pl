% ==== ../virage/src/test/resources/theories/ - Voting
% === component_type
% == aggregator
% max_aggregator
% == nat
% max
% min
% avg
% == termination_condition
% defer_eq_condition(nat)
% == alternative
% == set
% == rel
% == eval_func
% borda_score
% copeland_score
% minimax_score
% == comparator
% less
% leq
%
% === composable_module - electoral_module
% defer_module
% elect_module
% pass_module(nat, rel)
% drop_module(nat, rel)
% elimination_module(eval_func, nat, comparator)
% plurality_module
% blacks_rule
% borda_module
% classic_nanson
% copeland
% minimax
% nanson_baldwin
% schwartz_rule
%
% === compositional_structure
% downgrade(electoral_module)
% seq_comp(electoral_module, electoral_module)
% parallel_comp(electoral_module, electoral_module, aggregator)
% loop_comp(electoral_module, termination_condition)
%
% === property
% aggregator(aggregator)
% electoral_module(electoral_module)
% monotone(electoral_module)
% defer_monotone(electoral_module)
% defer_lift_invariant(electoral_module)
% non_blocking(electoral_module)
% electing(electoral_module)
% non_electing(electoral_module)
% defers(nat, electoral_module)
% rejects(nat,electoral_module)
% eliminates(nat,electoral_module)
% elects(nat,electoral_module)
% independent_of(electoral_module, set, alternative)
% disjoint_compatible(electoral_module, electoral_module)
% invariant_monotone(electoral_module)
% defer_invariant_monotone(electoral_module)
% commutative_agg(aggregator)
% conservative(aggregator)
% condorcet_consistent(electoral_module)
% defer_condorcet_consistent(electoral_module)
% condorcet_compatible(electoral_module)
%% decrementing(electoral_module)
%% defer_deciding(electoral_module)
%% rejecting(electoral_module)
%% eliminating(electoral_module)
% condorcet_rating(eval_func)
%% homogeneous(electoral_module)
%
% === composition_rule
% = max_aggregator.thy
% max_aggregator_sound
aggregator(max_aggregator).

% = defer_module.thy
% defer_module_sound
electoral_module(defer_module).
% = elect_module.thy
% elect_module_sound
electoral_module(elect_module).
% = plurality_module.thy
% plurality_module_sound
electoral_module(plurality_module).
% = pass_module.thy
% pass_module_sound
electoral_module(pass_module(_,_)).
% = drop_module.thy
% drop_module_sound
electoral_module(drop_module(_,_)).
% = elim_module.thy
% elim_module_sound
electoral_module(elimination_module(_,_,_)).
% = downgrade.thy
% downgrade_sound
electoral_module(downgrade(X)) :-
	electoral_module(X).
% = sequential_composition.thy
% seq_creates_modules
electoral_module(seq_comp(X,Y)) :-
	electoral_module(X),
	electoral_module(Y).
% = loop_composition.thy
% loop_comp_creates_modules
electoral_module(loop_comp(X,_)) :-
	electoral_module(X).
% = parallel_composition.thy
% par_creates_modules
electoral_module(parallel_comp(X,Y,A)) :-
	electoral_module(X),
	electoral_module(Y),
	aggregator(A).

% = electoral_modules.thy
% definition
defer_deciding(X) :-
	defers(1,X),
	non_electing(X).

% = condorcet_consistency.thy
% condorcet_compatibility_and_defer_deciding_implies_defer_condorcet_consistent
defer_condorcet_consistent(X) :-
	condorcet_compatible(X),
	defer_deciding(X).
% = elim_module.thy
% cr_eval_implies_max_elim_is_def_cc
defer_condorcet_consistent(elimination_module(E,_,max)) :-
	condorcet_rating(E).

% = copeland.thy
% copeland_module_is_cc
condorcet_consistent(seq_comp(elimination_module(copeland_score,max,less),elect_module)).
% = minimax.thy
% minimax_module_is_cc
condorcet_consistent(seq_comp(elimination_module(minimax_score,max,less),elect_module)).
% = voting_rule_constructors.thy
% m_defer_cc_implies_elector_m_cc
condorcet_consistent(seq_comp(X,elect_module)) :-
	defer_condorcet_consistent(X).
% = voting_rule_constructors.thy
% cr_eval_implies_elect_max_elim_is_cc
condorcet_consistent(seq_comp(elimination_module(E,_,max),elect_module)) :-
	condorcet_rating(E).

% = elim_module.thy
% cr_eval_implies_max_elim_is_ccomp
condorcet_compatible(elimination_module(E,_,max)) :-
	condorcet_rating(E).

% = minimax.thy
% minimax_score_is_condorcet_rating
condorcet_rating(minimax_score).

% = sequential_composition.thy 
% monotone_sequence
monotone(seq_comp(X,Y)) :-
	defer_lift_invariant(X),
	non_electing(X),
	defers(1,X),
	electing(Y).

% = electoral_modules.thy 
% strict_def_monotone_implies_def_monotone
defer_monotone(X) :- defer_lift_invariant(X).

% = defer_module.thy
% defer_module_non_electing
defer_lift_invariant(defer_module).
% = pass_module.thy
% pass_module_defer_lift_invariant
defer_lift_invariant(pass_module(_,_)).
% = drop_module.thy 
% drop_module_defer_lift_invariant
defer_lift_invariant(drop_module(_,_)).
% = sequential_composition.thy 
% defer_lift_invariant_seq
defer_lift_invariant(seq_comp(X,Y)) :-
	defer_lift_invariant(X),
	defer_lift_invariant(Y).
% = sequential_composition.thy 
% defer_invariant_monotone_to_defer_lift_invariant
defer_lift_invariant(seq_comp(X,Y)) :-
	defer_invariant_monotone(X),
	non_electing(Y),
	defers(1,Y),
	defer_monotone(Y).
% = parallel_composition.thy 
% defer_lift_invariant_par
defer_lift_invariant(parallel_comp(X,Y,max_aggregator)) :-
	disjoint_compatible(X,Y),
	defer_lift_invariant(X),
	defer_lift_invariant(Y).
% = loop_composition.thy 
% loop_comp_preserves_defer_lift_invariant
defer_lift_invariant(loop_comp(X,_)) :-
	defer_lift_invariant(X).

% = pass_module.thy
% pass_module_non_blocking
non_blocking(pass_module(_,_)).
% = downgrade.thy
% blocking_downgrade
non_blocking(downgrade(X)) :- electing(X).
% = sequential_composition.thy 
% seq_comp_preserves_non_blocking
non_blocking(seq_comp(X,Y)) :-
	non_blocking(X),
	non_blocking(Y). 
% = electoral_modules.thy
% electing_implies_non_blocking
non_blocking(X) :-
	electing(X).

% = elect_module.thy 
% elect_module_electing
electing(elect_module).
% = plurality_module.thy 
% plurality_module_electing
electing(plurality_module).
% = sequential_composition.thy
% seq_electing
electing(seq_comp(X,Y)) :-
	defers(1,X),
	electing(Y).

% = defer_module.thy 
% defer_module_defer_lift_invariant
non_electing(defer_module).
% = downgrade.thy 
% downgrade_non_electing
non_electing(downgrade(_)).
% = pass_module.thy 
% pass_module_non_electing
non_electing(pass_module(_,_)).
% = drop_module.thy
% drop_module_non_electing
non_electing(drop_module(_,_)).
% = elim_module.thy
% elim_module_nonelecting
non_electing(elimination_module(_,_,_)).
% = sequential_composition.thy
% seq_comp_preserves_non_electing
non_electing(seq_comp(X,Y)) :-
	non_electing(X),
	non_electing(Y).
% = parallel_composition.thy 
% conservative_agg_comp_preserves_non_electing
non_electing(parallel_comp(X,Y,A)) :-
	non_electing(X),
	non_electing(Y),
	conservative(A).
% = loop_composition.thy 
% loop_preserves_non_electing
non_electing(loop_comp(X,_)) :-
	non_electing(X).

% = pass_module.thy 
% pass_1_module_defers_1
defers(1, pass_module(1,_)).
% = pass_module.thy 
% pass_2_module_defers_2
defers(2, pass_module(2,_)).
% = unproven
% pass_N_module_defers_N
defers(N, pass_module(N,_)).
% = sequential_composition.thy 
% seq_comp_defers_1
defers(1,seq_comp(X,Y)) :-
	non_blocking(X),
	non_electing(X),
	defers(1,Y).
% = loop_composition.thy
% iterative_elimination_number_of_survivors_for_eliminates
defers(N, loop_comp(X, defer_eq_condition(N))) :-
	non_electing(X),
	eliminates(1,X).
	
% = drop_module.thy 
% drop_2_module_rejects_2
rejects(2, drop_module(2,_)).
% = unproven
% drop_N_module_rejects_N
rejects(N, drop_module(N,_)).

% = parallel_composition.thy 
% eliminates_1_par
eliminates(1,parallel_comp(X,Y,max_aggregator)) :-
	defers(1,X),
	non_electing(X),
	rejects(2,Y),
	disjoint_compatible(X,Y).

% = sequential_composition.thy 
% disjoint_compatible_seq
%% The '_' might be wrong, keep that in mind.
disjoint_compatible(seq_comp(X,_),Z) :-
	disjoint_compatible(X,Z).
% = parallel_composition.thy
% drop_pass_compatible
disjoint_compatible(drop_module(N,R), pass_module(N,R)).
% = electoral_modules.thy 
% disjoint_compatible_commutative
disjoint_compatible(X,Y) :-
	disjoint_compatible(Y,X).

% = plurality_module.thy 
% plurality_invariant_mono
invariant_monotone(plurality_module).

% = downgrade.thy 
% invariant_monotone_downgrade
defer_invariant_monotone(downgrade(X)) :- invariant_monotone(X).

% = max_aggregator.thy 
% max_aggregator_conservative
conservative(max_aggregator).


