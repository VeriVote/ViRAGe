% === component_type
% == aggregator
% max_aggregator
% == natural_number
% == termination_condition
% defer_eq_condition
% == alternative
% == set
%
% === composable_module - electoral_module
% defer_module
% elect_module
% pass_module(natural_number)
% drop_module(natural_number)
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
%
% === composition_rule
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


