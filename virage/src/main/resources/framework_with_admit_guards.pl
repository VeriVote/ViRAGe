admits_black(sequential_composition(condorcet_nonelecting,borda(_))).
admits_borda(sequential_composition(elim_module(max,borda_score),elect_module)).
admits_classic_nanson(sequential_composition(loop_composition(elim_module(leq_avg,borda_score),defer_eq_condition(1)),elect_module)).
admits_copeland(sequential_composition(elim_module(max,copeland_score),elect_module)).
admits_minimax(sequential_composition(elim_module(max,minimax_score),elect_module)).
admits_nanson_baldwin(sequential_composition(loop_composition(elim_module(min,borda_score),defer_eq_condition(1)),elect_module)).
admits_schwartz(sequential_composition(loop_composition(elim_module(less_avg,borda_score),defer_eq_condition(1)),elect_module)).
admits_defer_deciding(X) :- admits_defers(X,1),admits_non_electing(X).
admits_defer_condorcet_consistent(X) :- admits_condorcet_compatible(X),admits_defer_deciding(X).
admits_defer_condorcet_consistent(elim_module(max,_)).
admits_condorcet_consistent(X) :- admits_copeland(X).
admits_condorcet_consistent(X) :- admits_minimax(X).
admits_condorcet_consistent(sequential_composition(_,elect_module)).
admits_condorcet_consistent(sequential_composition(elim_module(max,_),elect_module)).
admits_condorcet_compatible(elim_module(max,_)).
admits_condorcet_rating(minimax_score).
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
admits_non_electing(elim_module(_,_)).
admits_non_electing(sequential_composition(_,_)).
admits_non_electing(parallel_composition(_,_,_)).
admits_non_electing(loop_composition(_,_)).
admits_defers(pass_module(1),1).
admits_defers(pass_module(2),2).
admits_defers(pass_module(_),_).
admits_defers(sequential_composition(_,_),1).
admits_defers(loop_composition(_,defer_eq_condition(_)),_).
admits_rejects(drop_module(2),2).
admits_rejects(drop_module(_),_).
admits_eliminates(parallel_composition(_,_,max_aggregator),1).
admits_disjoint_compatible(sequential_composition(_,_),_).
admits_disjoint_compatible(drop_module(_),pass_module(_)).
admits_disjoint_compatible(X,Y) :- admits_disjoint_compatible(Y,X).
admits_invariant_monotone(plurality_module).
admits_defer_invariant_monotone(downgrade(_)).
admits_conservative(max_aggregator).
black_wa(sequential_composition(condorcet_nonelecting,borda(_))).
borda_wa(sequential_composition(elim_module(max,borda_score),elect_module)).
classic_nanson_wa(sequential_composition(loop_composition(elim_module(leq_avg,borda_score),defer_eq_condition(1)),elect_module)).
copeland_wa(sequential_composition(elim_module(max,copeland_score),elect_module)).
minimax_wa(sequential_composition(elim_module(max,minimax_score),elect_module)).
nanson_baldwin_wa(sequential_composition(loop_composition(elim_module(min,borda_score),defer_eq_condition(1)),elect_module)).
schwartz_wa(sequential_composition(loop_composition(elim_module(less_avg,borda_score),defer_eq_condition(1)),elect_module)).
defer_deciding_wa(X) :- admits_defers(X,1),admits_non_electing(X),defers_wa(X,1),non_electing_wa(X).
defer_condorcet_consistent_wa(X) :- admits_condorcet_compatible(X),admits_defer_deciding(X),condorcet_compatible_wa(X),defer_deciding_wa(X).
defer_condorcet_consistent_wa(elim_module(max,F)) :- admits_condorcet_rating(F),condorcet_rating_wa(F).
condorcet_consistent_wa(X) :- admits_copeland(X),copeland_wa(X).
condorcet_consistent_wa(X) :- admits_minimax(X),minimax_wa(X).
condorcet_consistent_wa(sequential_composition(X,elect_module)) :- admits_defer_condorcet_consistent(X),defer_condorcet_consistent_wa(X).
condorcet_consistent_wa(sequential_composition(elim_module(max,F),elect_module)) :- admits_condorcet_rating(F),condorcet_rating_wa(F).
condorcet_compatible_wa(elim_module(max,F)) :- admits_condorcet_rating(F),condorcet_rating_wa(F).
condorcet_rating_wa(minimax_score).
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
non_electing_wa(elim_module(_,_)).
non_electing_wa(sequential_composition(X,Y)) :- admits_non_electing(X),admits_non_electing(Y),non_electing_wa(X),non_electing_wa(Y).
non_electing_wa(parallel_composition(X,Y,A)) :- admits_non_electing(X),admits_non_electing(Y),admits_conservative(A),non_electing_wa(X),non_electing_wa(Y),conservative_wa(A).
non_electing_wa(loop_composition(X,_)) :- admits_non_electing(X),non_electing_wa(X).
defers_wa(pass_module(1),1).
defers_wa(pass_module(2),2).
defers_wa(pass_module(N),N).
defers_wa(sequential_composition(X,Y),1) :- admits_non_blocking(X),admits_non_electing(X),admits_defers(Y,1),non_blocking_wa(X),non_electing_wa(X),defers_wa(Y,1).
defers_wa(loop_composition(_,defer_eq_condition(N)),N).
rejects_wa(drop_module(2),2).
rejects_wa(drop_module(N),N).
eliminates_wa(parallel_composition(X,Y,max_aggregator),1) :- admits_defers(X,1),admits_non_electing(X),admits_rejects(Y,2),admits_disjoint_compatible(X,Y),defers_wa(X,1),non_electing_wa(X),rejects_wa(Y,2),disjoint_compatible_wa(X,Y).
disjoint_compatible_wa(sequential_composition(X,_),Z) :- admits_disjoint_compatible(X,Z),disjoint_compatible_wa(X,Z).
disjoint_compatible_wa(drop_module(N),pass_module(N)).
disjoint_compatible_wa(X,Y) :- admits_disjoint_compatible(Y,X),disjoint_compatible_wa(Y,X).
invariant_monotone_wa(plurality_module).
defer_invariant_monotone_wa(downgrade(X)) :- admits_invariant_monotone(X),invariant_monotone_wa(X).
conservative_wa(max_aggregator).
