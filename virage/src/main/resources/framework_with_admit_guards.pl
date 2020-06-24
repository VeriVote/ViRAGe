admits_monotone(sequential_composition(_,_)).
admits_defer_monotone(X) :- admits_defer_lift_invariant(X).
admits_defer_lift_invariant(defer_module).
admits_defer_lift_invariant(pass_module(_)).
admits_defer_lift_invariant(drop_module(_)).
admits_defer_lift_invariant(sequential_composition(_,_)).
admits_defer_lift_invariant(sequential_composition(_,_)).
admits_defer_lift_invariant(parallel_composition(_,_,max_aggregator)).
admits_defer_lift_invariant(loop_composition(_,_)).
admits_non_blocking(pass_module(_)).
admits_non_blocking(downgrade(_)).
admits_non_blocking(sequential_composition(_,_)).
admits_non_blocking(X) :- admits_electing(X).
admits_electing(elect_module).
admits_electing(plurality_module).
admits_electing(sequential_composition(_,_)).
admits_non_electing(defer_module).
admits_non_electing(downgrade(_)).
admits_non_electing(pass_module(_)).
admits_non_electing(drop_module(_)).
admits_non_electing(sequential_composition(_,_)).
admits_non_electing(parallel_composition(_,_,_)).
admits_non_electing(loop_composition(_,_)).
admits_defers(pass_module(1),1).
admits_defers(pass_module(2),2).
admits_defers(pass_module(_),_).
admits_defers(sequential_composition(_,_),1).
admits_rejects(drop_module(2),2).
admits_rejects(drop_module(_),_).
admits_eliminates(parallel_composition(_,_,max_aggregator),1).
admits_disjoint_compatible(sequential_composition(_,_),_).
admits_disjoint_compatible(drop_module(_),pass_module(_)).
admits_disjoint_compatible(X,Y) :- admits_disjoint_compatible(Y,X).
admits_invariant_monotone(plurality_module).
admits_defer_invariant_monotone(downgrade(_)).
admits_conservative(max_aggregator).
monotone_wa(sequential_composition(X,Y)) :- admits_defer_lift_invariant(X),admits_non_electing(X),admits_defers(X,1),admits_electing(Y),defer_lift_invariant_wa(X),non_electing_wa(X),defers_wa(X,1),electing_wa(Y).
defer_monotone_wa(X) :- admits_defer_lift_invariant(X),defer_lift_invariant_wa(X).
defer_lift_invariant_wa(defer_module).
defer_lift_invariant_wa(pass_module(_)).
defer_lift_invariant_wa(drop_module(_)).
defer_lift_invariant_wa(sequential_composition(X,Y)) :- admits_defer_lift_invariant(X),admits_defer_lift_invariant(Y),defer_lift_invariant_wa(X),defer_lift_invariant_wa(Y).
defer_lift_invariant_wa(sequential_composition(X,Y)) :- admits_defer_invariant_monotone(X),admits_non_electing(Y),admits_defers(Y,1),admits_defer_monotone(Y),defer_invariant_monotone_wa(X),non_electing_wa(Y),defers_wa(Y,1),defer_monotone_wa(Y).
defer_lift_invariant_wa(parallel_composition(X,Y,max_aggregator)) :- admits_disjoint_compatible(X,Y),admits_defer_lift_invariant(X),admits_defer_lift_invariant(Y),disjoint_compatible_wa(X,Y),defer_lift_invariant_wa(X),defer_lift_invariant_wa(Y).
defer_lift_invariant_wa(loop_composition(X,_)) :- admits_defer_lift_invariant(X),defer_lift_invariant_wa(X).
non_blocking_wa(pass_module(_)).
non_blocking_wa(downgrade(X)) :- admits_electing(X),electing_wa(X).
non_blocking_wa(sequential_composition(X,Y)) :- admits_non_blocking(X),admits_non_blocking(Y),non_blocking_wa(X),non_blocking_wa(Y).
non_blocking_wa(X) :- admits_electing(X),electing_wa(X).
electing_wa(elect_module).
electing_wa(plurality_module).
electing_wa(sequential_composition(X,Y)) :- admits_defers(X,1),admits_electing(Y),defers_wa(X,1),electing_wa(Y).
non_electing_wa(defer_module).
non_electing_wa(downgrade(_)).
non_electing_wa(pass_module(_)).
non_electing_wa(drop_module(_)).
non_electing_wa(sequential_composition(X,Y)) :- admits_non_electing(X),admits_non_electing(Y),non_electing_wa(X),non_electing_wa(Y).
non_electing_wa(parallel_composition(X,Y,A)) :- admits_non_electing(X),admits_non_electing(Y),admits_conservative(A),non_electing_wa(X),non_electing_wa(Y),conservative_wa(A).
non_electing_wa(loop_composition(X,_)) :- admits_non_electing(X),non_electing_wa(X).
defers_wa(pass_module(1),1).
defers_wa(pass_module(2),2).
defers_wa(pass_module(N),N).
defers_wa(sequential_composition(X,Y),1) :- admits_non_blocking(X),admits_non_electing(X),admits_defers(Y,1),non_blocking_wa(X),non_electing_wa(X),defers_wa(Y,1).
rejects_wa(drop_module(2),2).
rejects_wa(drop_module(N),N).
eliminates_wa(parallel_composition(X,Y,max_aggregator),1) :- admits_defers(X,1),admits_non_electing(X),admits_rejects(Y,2),admits_disjoint_compatible(X,Y),defers_wa(X,1),non_electing_wa(X),rejects_wa(Y,2),disjoint_compatible_wa(X,Y).
disjoint_compatible_wa(sequential_composition(X,_),Z) :- admits_disjoint_compatible(X,Z),disjoint_compatible_wa(X,Z).
disjoint_compatible_wa(drop_module(N),pass_module(N)).
disjoint_compatible_wa(X,Y) :- admits_disjoint_compatible(Y,X),disjoint_compatible_wa(Y,X).
invariant_monotone_wa(plurality_module).
defer_invariant_monotone_wa(downgrade(X)) :- admits_invariant_monotone(X),invariant_monotone_wa(X).
conservative_wa(max_aggregator).
