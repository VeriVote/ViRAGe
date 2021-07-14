%% The Extended Prolog [(E)PL] format is used to represent compositional frameworks.
%% It is used by ViRAGe to represent and persist its data inbetween executions.
%%
%% While this file is a valid (E)PL file, it is mostly meant to document the
%% format itself.
%% 
%% Every (E)PL file is a valid Prolog knowledge base, so all of the extensions
%% take place within Prolog comments, lines starting with the '%' character.
%% Lines starting with '%%' are (E)PL comments, and are ignored by both 
%% Prolog and (E)PL parsers.
%%
%% An (E)PL file is usually built automatically from an Isabelle session.
%% This session is referenced by the following two parameters, where
%% $ROOT_PATH points to the session's ROOT file, and $SESSION_NAME being
%% just that.
% ==== $ROOT_PATH - $SESSION_NAME
%
%% A component type is a collection of base modules and compositional
%% structures used to build more complex modules. All of these components
%% are listed below their corresponding type name.
%% Any component may have a list of parameters, specified using their
%% types. Empty brackets may be omitted.
%% 
%% In general, a component type looks as follows:
%% % == $NAME
%% % $MODULE_1($PARAMETERS)
%% % $MODULE_2($PARAMETERS)
%% % ...
% === COMPONENT_TYPE
% == type_a
% base_module_a_1()
% base_module_a_2
% comp_struct_a_1(type_a,type_a)
% == type_b
% base_module_b_1(type_a)
% comp_struct_b_1(type_a,type_b)
%
%% The following section is very similar to the one above, but it contains
%% only the properties that components may or may not have.
% === PROPERTY
% property_a(type_a)
% property_b(type_b)
% property_a_b(type_a,type_b)
%
%% This last section contains the composition rules. These contain information
%% about which components satisfy which properties and how the properties
%% of a component might influence the properties of larger compositions.
%% In general, a composition rule is defined as follows:
%%
%% % = $ORIGIN
%% % $NAME
%% $PROLOG_CLAUSE
%% 
%% The $ORIGIN specifies the Isabelle theory this rule originates from, or can
%% be either "UNPROVEN" if the rule was added by the user without a formal proof
%% or "ASSUMPTION" if the rule was added automatically by ViRAGe.
%% $NAME specifies the symbolic name of a rule, as it will be used when the rule
%% appears in Isabelle proofs.
%% Finally, the $PROLOG_CLAUSE contains the semantics of the rule.
% === COMPOSITION_RULE
% = UNPROVEN
% base_module_a_1_has_property_a
property_a(base_module_a_1).

% = UNPROVEN
% base_module_a_2_has_property_a
property_a(base_module_a_2).

% = UNPROVEN
% comp_struct_a_1_preserves_property_a
property_a(comp_struct_a_1(X,Y)) :- property_a(X), property_a(Y).

% = UNPROVEN
% introduction_of_property_b
property_b(comp_struct_b_1(A,_)) :- property_a(A).

% = UNPROVEN
% property_a_b_intro
property_a_b(A,B) :- property_a(A), property_b(B).

%% Reserved Keywords (currently both in upper- and lowercase):
%% UNPROVEN
%% ASSUMPTION
%% COMPONENT_TYPE
%% PROPERTY
%% COMPOSITION_RULE
