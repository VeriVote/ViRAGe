expand([Node | Path], ExpandedPaths) :-
bagof(
[Node1, Node | Path],
(s(Node, Node1), \+ member(Node1, Path)),
ExpandedPaths).
expand([Node | Path], ExpandedPaths) :-
bagof(
[Node1, Node | Path],
(s(Node, Node1), \+ member(Node1, Path)),
ExpandedPaths),
!.
expand(Path, []).

%% breadth_first_search(+Node, -Path)
breadth_first_search(Node, Path) :-
bf_search_aux([[Node]], Path).

bf_search_aux([[Node | Path] | _], [Node | Path]) :-
goal(Node).
bf_search_aux([CurrentPath | NextPaths], FinalPath) :-
expand(CurrentPath, ExpandedPaths),
append(NextPaths, ExpandedPaths, NewPaths),
bf_search_aux(NewPaths, FinalPath).
