% === component_type
% == type_a
% a
% a2
% == type_b
% b
%
% === composable_module
% module_1
% module_2
%
% === compositional_structure
% simple_comp(composable_module, composable_module)
%
% === property
% property_a(type_a)
% property_b(type_a, composable_module)
% property_c(type_a, type_b)
%
% === composition_rule
% = origin
% fact_a
property_a(a).
% = origin
% rule_a
property_a(X) :-
	property_b(X,_).

% = origin2
% rule_b
property_c(X,Y) :-
	property_a(X),
	property_b(X, module_1).
