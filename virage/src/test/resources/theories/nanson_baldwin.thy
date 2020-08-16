theory nanson_baldwin
  imports voting_rule_constructors borda_module

begin

(**********************************************)
(*** Definition: Nanson-Baldwin Voting Rule ***)
(**********************************************)

definition Nanson_Baldwin :: "'a Electoral_module" where
  "Nanson_Baldwin \<equiv> iterelect(MIN_Eliminator Borda_score)"

end