theory condorcet_module
imports electoral_modules eval_func misk_elim_rules borda_module

begin

(*************************************)
(*** Definition: Condorcet Voting Rule ***)
(*************************************)

fun Condorcet_score:: "'a Eval_function" where
  "Condorcet_score x A p = 
  (if (condorcet_winner_in A p x) then 1 else 0)"

definition Condorcet :: "'a Electoral_module" where
  "Condorcet \<equiv> elector(MAX_Eliminator Condorcet_score)"

definition Condorcet_Nonelecting :: "'a Electoral_module" where
  "Condorcet_Nonelecting \<equiv> (MAX_Eliminator Condorcet_score)"

definition Condorcet' :: "'a Electoral_module" where
  "Condorcet' \<equiv> iterelect(MIN_Eliminator Condorcet_score)"

(***************)
(*** Lemmata ***)
(***************)

(* Condorcet_score is condorcet rating *)
lemma condorcet_score_is_condorcet_rating:
  shows "condorcet_rating Condorcet_score"
  by (simp add: condorcet_rating_def unique_condorcet_winner)

corollary condorcet_module_is_cc:
  shows "condorcet_consistent Condorcet"
proof -
  have "\<not> defer_condorcet_consistent (\<lambda>A. MAX_Eliminator Condorcet_score (A::'a set)) \<or> condorcet_consistent (Condorcet::'a set \<Rightarrow> (_ \<times> _) set list \<Rightarrow> _ set \<times> _ set \<times> _ set)"
    by (simp add: Condorcet_def m_defer_cc_implies_elector_m_cc)
  then show ?thesis
    using condorcet_score_is_condorcet_rating cr_eval_implies_max_elim_is_def_cc by blast
qed

end