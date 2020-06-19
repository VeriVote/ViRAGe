monotone(sequential_composition(X,Y)) :- defer_lift_invariant(X), non_electing(X), defers(X,1), electing(Y).
defer_monotone(X) :- defer_lift_invariant(X).
defer_lift_invariant(defer_module).
defer_lift_invariant(pass_module(_)).
defer_lift_invariant(drop_module(_)).
defer_lift_invariant(sequential_composition(X,Y)) :- defer_lift_invariant(X), defer_lift_invariant(Y).
defer_lift_invariant(sequential_composition(X,Y)) :- defer_invariant_monotone(X), non_electing(Y), defers(Y,1), defer_monotone(Y).
defer_lift_invariant(parallel_composition(X,Y,max_aggregator)) :- disjoint_compatible(X,Y), defer_lift_invariant(X), defer_lift_invariant(Y).
defer_lift_invariant(loop_composition(X,_)) :- defer_lift_invariant(X).
non_blocking(pass_module(_)).
non_blocking(downgrade(X)) :- electing(X).
non_blocking(sequential_composition(X,Y)) :- non_blocking(X), non_blocking(Y). 
non_blocking(X) :- electing(X).
electing(elect_module).
electing(plurality_module).
electing(sequential_composition(X,Y)) :- defers(X,1), electing(Y).
non_electing(defer_module).
non_electing(downgrade(_)).
non_electing(pass_module(_)).
non_electing(drop_module(_)).
non_electing(sequential_composition(X,Y)) :- non_electing(X), non_electing(Y).
non_electing(parallel_composition(X,Y,A)) :- non_electing(X), non_electing(Y), conservative(A).
non_electing(loop_composition(X,_)) :- non_electing(X).
defers(pass_module(1), 1).
defers(pass_module(2), 2).
defers(pass_module(N), N).
defers(sequential_composition(X,Y), 1) :- non_blocking(X), non_electing(X), defers(Y,1).
rejects(drop_module(2), 2).
rejects(drop_module(N), N).
eliminates(parallel_composition(X,Y,max_aggregator),1) :- defers(X,1), non_electing(X), rejects(Y,2), disjoint_compatible(X,Y).
disjoint_compatible(sequential_composition(X,_),Z) :- disjoint_compatible(X,Z).
disjoint_compatible(drop_module(N), pass_module(N)).
disjoint_compatible(X,Y) :- disjoint_compatible(Y,X).
invariant_monotone(plurality_module).
defer_invariant_monotone(downgrade(X)) :- invariant_monotone(X).
conservative(max_aggregator).


