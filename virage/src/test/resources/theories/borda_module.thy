theory borda_module
  imports voting_rule_constructors eval_func electoral_modules elim_module
begin

(*************************************)
(*** Definition: Borda Voting Rule ***)
(*************************************)

fun Borda_score :: "'a Eval_function" where
  "Borda_score x A p = (\<Sum>y \<in> A. (prefer_count p x y))"

fun Borda_score_code :: "'a Eval_function" where
  "Borda_score_code x A p = (\<Sum>y \<in> A. (prefer_count_code p x y))"

export_code Borda_score_code in Haskell

definition Borda :: "'a Electoral_module" where
  "Borda \<equiv> elector(MAX_Eliminator Borda_score)"

definition Borda_code :: "'a Electoral_module" where
  "Borda_code \<equiv> elector(MAX_Eliminator Borda_score_code)"

export_code Borda_code in Haskell

end
