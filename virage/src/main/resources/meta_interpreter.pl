prove(true, true) :- !.

prove((G1, G2), (P1, P2)) :- 
   !,
   prove(G1, P1), 
   prove(G2, P2).

prove((G1;_), P1) :- prove(G1, P1).
prove((_;G2), P2) :- !, prove(G2, P2).

prove(H, subgoal(H, Goal)) :- clause(H, Body), prove(Body, Goal).
