% Taken from https://www.metalevel.at/acomip/

:- use_module(library(clpfd)).

mi_clause(G, Body) :-
        clause(G, B),
        defaulty_better(B, Body).

defaulty_better(true, true).
defaulty_better((A,B), (BA,BB)) :-
        defaulty_better(A, BA),
        defaulty_better(B, BB).
defaulty_better(G, g(G)) :-
        G \= true,
        G \= (_,_).

:- op(750, xfy, =>).

mi_tree(true, true).
mi_tree((A,B), (TA,TB)) :-
        mi_tree(A, TA),
        mi_tree(B, TB).
mi_tree(g(G), TBody => G) :-
        mi_clause(G, Body),
        mi_tree(Body, TBody).

mi_limit(Goal, Max) :-
        mi_limit(Goal, Max, _).

mi_limit(true, N, N).
mi_limit((A,B), N0, N) :-
        mi_limit(A, N0, N1),
        mi_limit(B, N1, N).
mi_limit(g(G), N0, N) :-
        N0 #> 0,
        N1 #= N0 - 1,
        mi_clause(G, Body),
        mi_limit(Body, N1, N).

mi_id(Goal) :-
        length(_, N),
        mi_limit(Goal, N).
