theory borda_module
  imports voting_rule_constructors eval_func electoral_modules elim_module
begin

(*************************************)
(*** Definition: Borda Voting Rule ***)
(*************************************)

fun Borda_score :: "'a Eval_function" where
  "Borda_score x A p = (\<Sum>y \<in> A. (prefer_count p x y))"

definition Borda :: "'a Electoral_module" where
  "Borda \<equiv> elector(MAX_Eliminator Borda_score)"

end
