theory schwartz_rule
  imports voting_rule_constructors borda_module

begin

(****************************************)
(*** Definition: Schwartz Voting Rule ***)
(****************************************)

definition Schwartz :: "'a Electoral_module" where
  "Schwartz \<equiv> iterelect(LESS_AVG_Eliminator Borda_score)"

definition Schwartz_code :: "'a Electoral_module" where
  "Schwartz_code \<equiv> iterelect(LESS_AVG_Eliminator Borda_score_code)"

end
