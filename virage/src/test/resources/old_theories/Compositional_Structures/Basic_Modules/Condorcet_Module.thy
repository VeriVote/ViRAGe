(*  File:       Condorcet_Module.thy
    Copyright   2021  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Stephan Bohr, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Michael Kirsten, Karlsruhe Institute of Technology (KIT)"\<close>

section \<open>Condorcet Module\<close>

theory Condorcet_Module
  imports "Component_Types/Elimination_Module"
begin

text
\<open>This is the Condorcet module used by the Condorcet (voting) rule. The Condorcet
rule is a voting rule that implements the Condorcet criterion, i.e., it elects
the Condorcet winner if it exists, otherwise a tie remains between all
alternatives. The module implemented herein only rejects the alternatives not
elected by the voting rule, and defers the alternatives that would be elected
by the full voting rule.\<close>

subsection \<open>Definition\<close>

fun condorcet_score :: "'a Evaluation_Function" where
  "condorcet_score x A p =
    (if (condorcet_winner A p x) then 1 else 0)"

fun condorcet_score_code :: "'a Evaluation_Function" where
  "condorcet_score_code x A p =
    (if (condorcet_winner_code A p x) then 1 else 0)"

fun condorcet :: "'a Electoral_Module" where
  "condorcet A p = (max_eliminator condorcet_score) A p"

fun condorcet_code :: "'a Electoral_Module" where
  "condorcet_code A p =
    (max_eliminator condorcet_score_code) A p"

subsection \<open>Property\<close>

(* Condorcet score is Condorcet rating. *)
theorem condorcet_score_is_condorcet_rating: "condorcet_rating condorcet_score"
proof -
  have
    "\<forall>f.
      (\<not> condorcet_rating f \<longrightarrow>
          (\<exists>A rs a.
            condorcet_winner A rs a \<and>
              (\<exists>aa. \<not> f (aa::'a) A rs < f a A rs \<and> a \<noteq> aa \<and> aa \<in> A))) \<and>
        (condorcet_rating f \<longrightarrow>
          (\<forall>A rs a. condorcet_winner A rs a \<longrightarrow>
            (\<forall>aa. f aa A rs < f a A rs \<or> a = aa \<or> aa \<notin> A)))"
    unfolding condorcet_rating_def
    by (metis (mono_tags, hide_lams))
  thus ?thesis
    using cond_winner_unique condorcet_score.simps zero_less_one
    by (metis (no_types))
qed

theorem condorcet_is_dcc: "defer_condorcet_consistency condorcet"
proof -
  have max_cscore_dcc:
    "defer_condorcet_consistency (max_eliminator condorcet_score)"
    using cr_eval_imp_dcc_max_elim
    by (simp add: condorcet_score_is_condorcet_rating)
  have cond_eq_max_cond:
    "\<And>A p. (condorcet A p \<equiv> max_eliminator condorcet_score A p)"
    by simp
  from max_cscore_dcc cond_eq_max_cond show ?thesis
    unfolding defer_condorcet_consistency_def electoral_module_def
    by (smt (verit, ccfv_threshold))
qed

end
