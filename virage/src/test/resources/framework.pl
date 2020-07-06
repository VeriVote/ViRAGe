% === component_type
% == aggregator
% max_aggregator
% == natural_number
% == termination_condition
% defer_eq_condition(natural_number)
% == alternative
% == set
% == eval_func
% borda_score
% copeland_score
% minimax_score
% == comparator
% less
% max
% leq
% min
% avg
% less_avg
% leq_avg
%
% === composable_module - electoral_module
% defer_module
% elect_module
% pass_module(natural_number)
% drop_module(natural_number)
%% threshold value is omitted here.
% elim_module(eval_func,comparator)
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
% sequential_composition(electoral_module, electoral_module)
% parallel_composition(electoral_module, electoral_module, aggregator)
% loop_composition(electoral_module, termination_condition)
%
% === property
% monotone(electoral_module)
% defer_monotone(electoral_module)
% defer_lift_invariant(electoral_module)
% non_blocking(electoral_module)
% electing(electoral_module)
% non_electing(electoral_module)
% defers(electoral_module, natural_number)
% rejects(electoral_module, natural_number)
% eliminates(electoral_module, natural_number)
% elects(electoral_module, natural_number)
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
% = blacks_rule.thy
% definition
black(sequential_composition(condorcet_nonelecting, borda(_))).

% = borda_module.thy
% definition
borda(sequential_composition(elim_module(max,borda_score),elect_module)).

% = classic_nanson.thy
% definition
classic_nanson(sequential_composition(loop_composition(elim_module(leq_avg, borda_score), defer_eq_condition(1)), elect_module)).

% = copeland.thy
% definition
copeland(sequential_composition(elim_module(max,copeland_score),elect_module)).

% = minimax.thy
% definition
minimax(sequential_composition(elim_module(max,minimax_score),elect_module)).

% = nanson_baldwin.thy
% definition
nanson_baldwin(sequential_composition(loop_composition(elim_module(min,borda_score),defer_eq_condition(1)),elect_module)).

% = schwartz_rule.thy
% definition
schwartz(sequential_composition(loop_composition(elim_module(less_avg,borda_score),defer_eq_condition(1)),elect_module)).

% = electoral_modules.thy
% definition
defer_deciding(X) :-
	defers(X,1),
	non_electing(X).

% = condorcet_consistency.thy
% condorcet_compatibility_and_defer_deciding_implies_defer_condorcet_consistent
defer_condorcet_consistent(X) :-
	condorcet_compatible(X),
	defer_deciding(X).
% = elim_module.thy
% cr_eval_implies_max_elim_is_def_cc
defer_condorcet_consistent(elim_module(max,F)) :-
	condorcet_rating(F).

% = copeland.thy
% copeland_module_is_cc
condorcet_consistent(X) :-
	copeland(X).
% = minimax.thy
% minimax_module_is_cc
condorcet_consistent(X) :-
	minimax(X).
% = voting_rule_constructors.thy
% m_defer_cc_implies_elector_m_cc
condorcet_consistent(sequential_composition(X,elect_module)) :-
	defer_condorcet_consistent(X).
% = voting_rule_constructors.thy
% cr_eval_implies_elect_max_elim_is_cc
condorcet_consistent(sequential_composition(elim_module(max,F),elect_module)) :-
	condorcet_rating(F).

% = elim_module.thy
% cr_eval_implies_max_elim_is_ccomp
condorcet_compatible(elim_module(max,F)) :-
	condorcet_rating(F).

% = minimax.thy
% minimax_score_is_condorcet_rating
condorcet_rating(minimax_score).

% = sequential_composition.thy 
% monotone_sequence
monotone(sequential_composition(X,Y)) :-
	defer_lift_invariant(X),
	non_electing(X),
	defers(X,1),
	electing(Y).

% = electoral_module.thy 
% strict_def_monotone_implies_def_monotone
defer_monotone(X) :- defer_lift_invariant(X).

% = defer_module.thy
% defer_module_non_electing
defer_lift_invariant(defer_module).
% = pass_module.thy
% pass_module_defer_lift_invariant
defer_lift_invariant(pass_module(_)).
% = drop_module.thy 
% drop_module_defer_lift_invariant
defer_lift_invariant(drop_module(_)).
% = sequential_composition.thy 
% defer_lift_invariant_seq
defer_lift_invariant(sequential_composition(X,Y)) :-
	defer_lift_invariant(X),
	defer_lift_invariant(Y).
% = sequential_composition.thy 
% defer_invariant_monotone_to_defer_lift_invariant
defer_lift_invariant(sequential_composition(X,Y)) :-
	defer_invariant_monotone(X),
	non_electing(Y),
	defers(Y,1),
	defer_monotone(Y).
% = parallel_composition.thy 
% defer_lift_invariant_par
defer_lift_invariant(parallel_composition(X,Y,max_aggregator)) :-
	disjoint_compatible(X,Y),
	defer_lift_invariant(X),
	defer_lift_invariant(Y).
% = loop_composition.thy 
% loop_comp_preserves_defer_lift_invariant
defer_lift_invariant(loop_composition(X,_)) :-
	defer_lift_invariant(X).

% = pass_module.thy
% pass_module_non_blocking
non_blocking(pass_module(_)).
% = downgrade.thy
% blocking_downgrade
non_blocking(downgrade(X)) :- electing(X).
% = sequential_composition.thy 
% seq_comp_preserves_non_blocking
non_blocking(sequential_composition(X,Y)) :-
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
electing(sequential_composition(X,Y)) :-
	defers(X,1),
	electing(Y).

% = defer_module.thy 
% defer_module_defer_lift_invariant
non_electing(defer_module).
% = downgrade.thy 
% downgrade_non_electing
non_electing(downgrade(_)).
% = pass_module.thy 
% pass_module_non_electing
non_electing(pass_module(_)).
% = drop_module.thy
% drop_module_non_electing
non_electing(drop_module(_)).
% = elim_module.thy
% elim_module_nonelecting
non_electing(elim_module(_,_)).
% = sequential_composition.thy
% seq_comp_preserves_non_electing
non_electing(sequential_composition(X,Y)) :-
	non_electing(X),
	non_electing(Y).
% = parallel_composition.thy 
% conservative_agg_comp_preserves_non_electing
non_electing(parallel_composition(X,Y,A)) :-
	non_electing(X),
	non_electing(Y),
	conservative(A).
% = loop_composition.thy 
% loop_preserves_non_electing
non_electing(loop_composition(X,_)) :-
	non_electing(X).

% = pass_module.thy 
% pass_1_module_defers_1
defers(pass_module(1), 1).
% = pass_module.thy 
% pass_2_module_defers_2
defers(pass_module(2), 2).
% = unproven
% pass_N_module_defers_N
defers(pass_module(N), N).
% = sequential_composition.thy 
% seq_comp_defers_1
defers(sequential_composition(X,Y), 1) :-
	non_blocking(X),
	non_electing(X),
	defers(Y,1).
% = unproven
% loop_defer_eq_N_defers_N
defers(loop_composition(_, defer_eq_condition(N)),N).
	
% = drop_module.thy 
% drop_2_module_rejects_2
rejects(drop_module(2), 2).
% = unproven
% drop_N_module_rejects_N
rejects(drop_module(N), N).

% = parallel_composition.thy 
% eliminates_1_par
eliminates(parallel_composition(X,Y,max_aggregator),1) :-
	defers(X,1),
	non_electing(X),
	rejects(Y,2),
	disjoint_compatible(X,Y).

% = sequential_composition.thy 
% disjoint_compatible_seq
%% The '_' might be wrong, keep that in mind.
%% Potential solution: Add predicate 'electoral_module'.
disjoint_compatible(sequential_composition(X,_),Z) :-
	disjoint_compatible(X,Z).
% = parallel_composition.thy
% drop_pass_compatible
disjoint_compatible(drop_module(N), pass_module(N)).
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


