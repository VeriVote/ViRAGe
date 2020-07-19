theory classic_nanson
  imports voting_rule_constructors borda_module

begin

(**********************************************)
(*** Definition: Classic Nanson Voting Rule ***)
(**********************************************)

definition Classic_nanson :: "'a Electoral_module" where
  "Classic_nanson \<equiv> iterelect(LEQ_AVG_Eliminator Borda_score)"

end