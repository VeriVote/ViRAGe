(*  File:       Copeland_Module.thy
    Copyright   2021  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Stephan Bohr, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Michael Kirsten, Karlsruhe Institute of Technology (KIT)"\<close>

section \<open>Copeland Module\<close>

theory Copeland_Module
  imports "Component_Types/Elimination_Module"
begin

text
\<open>This is the Copeland module used by the Copeland voting rule. The Copeland
rule elects the alternatives with the highest difference between the amount
of simple-majority wins and the amount of simple-majority losses. The module
implemented herein only rejects the alternatives not elected by the voting
rule, and defers the alternatives that would be elected by the full voting
rule.\<close>

subsection \<open>Definition\<close>

fun copeland_score :: "'a Evaluation_Function" where
  "copeland_score x A p =
    card{y \<in> A . wins x p y} - card{y \<in> A . wins y p x}"

fun copeland_score_code :: "'a Evaluation_Function" where
  "copeland_score_code x A p =
    card{y \<in> A . wins_code x p y} - card{y \<in> A . wins_code y p x}"

fun copeland :: "'a Electoral_Module" where
  "copeland A p = max_eliminator copeland_score A p"

fun copeland_code :: "'a Electoral_Module" where
  "copeland_code A p =
    max_eliminator copeland_score_code A p"

subsection \<open>Lemmata\<close>

(*For a Condorcet winner w, we have: card{y \<in> A . wins x p y} = |A|-1*)
lemma cond_winner_imp_win_count:
  assumes winner: "condorcet_winner A p w"
  shows "card {y \<in> A . wins w p y} = card A -1"
proof -
  from winner
  have 0: "\<forall>x \<in> A - {w} . wins w p x"
    by simp
  have 1: "\<forall>M . {x \<in> M . True} = M"
    by blast
  from 0 1
  have "{x \<in> A - {w} . wins w p x} = A - {w}"
    by blast
  hence 10: "card {x \<in> A - {w} . wins w p x} = card (A - {w})"
    by simp
  from winner
  have 11: "w \<in> A"
    by simp
  hence "card (A - {w}) = card A - 1"
    using card_Diff_singleton condorcet_winner.simps winner
    by metis
  hence amount1:
    "card {x \<in> A - {w} . wins w p x} = card (A) - 1"
    using "10"
    by linarith
  have 2: "\<forall>x \<in> {w} . \<not> wins x p x"
    by (simp add: wins_irreflex)
  have 3: "\<forall>M . {x \<in> M . False} = {}"
    by blast
  from 2 3
  have "{x \<in> {w} . wins w p x} = {}"
    by blast
  hence amount2: "card {x \<in> {w} . wins w p x} = 0"
    by simp
  have disjunct:
    "{x \<in> A - {w} . wins w p x} \<inter> {x \<in> {w} . wins w p x} = {}"
    by blast
  have union:
    "{x \<in> A - {w} . wins w p x} \<union> {x \<in> {w} . wins w p x} =
        {x \<in> A . wins w p x}"
    using "2"
    by blast
  have finiteness1: "finite {x \<in> A - {w} . wins w p x}"
    using condorcet_winner.simps winner
    by fastforce
  have finiteness2: "finite {x \<in> {w} . wins w p x}"
    by simp
  from finiteness1 finiteness2 disjunct card_Un_disjoint
  have
    "card ({x \<in> A - {w} . wins w p x} \<union> {x \<in> {w} . wins w p x}) =
        card {x \<in> A - {w} . wins w p x} + card {x \<in> {w} . wins w p x}"
    by blast
  with union
  have "card {x \<in> A . wins w p x} =
          card {x \<in> A - {w} . wins w p x} + card {x \<in> {w} . wins w p x}"
    by simp
  with amount1 amount2
  show ?thesis
    by linarith
qed

(*For a Condorcet winner w, we have: card{y \<in> A . wins y p x} = 0*)
lemma cond_winner_imp_loss_count:
  assumes winner: "condorcet_winner A p w"
  shows "card {y \<in> A . wins y p w} = 0"
  using Collect_empty_eq card_eq_0_iff condorcet_winner.simps
        insert_Diff insert_iff wins_antisym winner
  by (metis (no_types, lifting))

(*Copeland Score of a Condorcet Winner*)
lemma cond_winner_imp_copeland_score:
  assumes winner: "condorcet_winner A p w"
  shows "copeland_score w A p = card A -1"
  unfolding copeland_score.simps
proof -
  show
    "card {y \<in> A. wins w p y} - card {y \<in> A. wins y p w} =
      card A - 1"
    using cond_winner_imp_loss_count
        cond_winner_imp_win_count winner
  proof -
    have f1: "card {a \<in> A. wins w p a} = card A - 1"
      using cond_winner_imp_win_count winner
      by simp
    have f2: "card {a \<in> A. wins a p w} = 0"
      using cond_winner_imp_loss_count winner
      by (metis (no_types))
    have "card A - 1 - 0 = card A - 1"
      by simp
    thus ?thesis
      using f2 f1
      by simp
  qed
qed

(*
   For a non-Condorcet winner l, we have:
   card{y \<in> A . wins x p y} <= |A|-1 -1
*)
lemma non_cond_winner_imp_win_count:
  assumes
    winner: "condorcet_winner A p w" and
    loser: "l \<noteq> w" and
    l_in_A: "l \<in> A"
  shows "card {y \<in> A . wins l p y} <= card A - 2"
proof -
  from winner loser l_in_A
  have "wins w p l"
    by simp
  hence 0: "\<not> wins l p w"
    by (simp add: wins_antisym)
  have 1: "\<not> wins l p l"
    by (simp add: wins_irreflex)
  from 0 1 have 2:
    "{y \<in> A . wins l p y} =
        {y \<in> A-{l,w} . wins l p y}"
    by blast
  have 3: "\<forall> M f . finite M \<longrightarrow> card {x \<in> M . f x} \<le> card M"
    by (simp add: card_mono)
  have 4: "finite (A-{l,w})"
    using condorcet_winner.simps finite_Diff winner
    by metis
  from 3 4 have 5:
    "card {y \<in> A-{l,w} . wins l p y} \<le>
      card (A-{l,w})"
    by (metis (full_types))
  have "w \<in> A"
    using condorcet_winner.simps winner
    by metis
  with l_in_A
  have "card(A-{l,w}) = card A - card {l,w}"
    by (simp add: card_Diff_subset)
  hence "card(A-{l,w}) = card A - 2"
    by (simp add: loser)
  with 5 2
  show ?thesis
    by simp
qed

subsection \<open>Property\<close>

(*The Copeland score is Condorcet rating*)
theorem copeland_score_is_cr: "condorcet_rating copeland_score"
  unfolding condorcet_rating_def
proof (unfold copeland_score.simps, safe)
  fix
    A :: "'a set" and
    p :: "'a Profile" and
    w :: "'a" and
    l :: "'a"
  assume
    winner: "condorcet_winner A p w" and
    l_in_A: "l \<in> A" and
    l_neq_w: "l \<noteq> w"
  show
    "card {y \<in> A. wins l p y} - card {y \<in> A. wins y p l}
        < card {y \<in> A. wins w p y} - card {y \<in> A. wins y p w}"
  proof -
    from winner have 0:
      "card {y \<in> A. wins w p y} - card {y \<in> A. wins y p w} =
        card A -1"
      using cond_winner_imp_copeland_score
      by fastforce
    from winner l_neq_w l_in_A have 1:
      "card {y \<in> A. wins l p y} - card {y \<in> A. wins y p l} \<le>
          card A -2"
      using non_cond_winner_imp_win_count
      by fastforce
    have 2: "card A -2 < card A -1"
      using card_0_eq card_Diff_singleton
            condorcet_winner.simps diff_less_mono2
            empty_iff finite_Diff insertE insert_Diff
            l_in_A l_neq_w neq0_conv one_less_numeral_iff
            semiring_norm(76) winner zero_less_diff
      by metis
    hence
      "card {y \<in> A. wins l p y} - card {y \<in> A. wins y p l} <
        card A -1"
      using "1" le_less_trans
      by blast
    with 0
    show ?thesis
      by linarith
  qed
qed

theorem copeland_is_dcc: "defer_condorcet_consistency copeland"
proof -
  have max_cplscore_dcc:
    "defer_condorcet_consistency (max_eliminator copeland_score)"
    using cr_eval_imp_dcc_max_elim
    by (simp add: copeland_score_is_cr)
  have copel_eq_max_copel:
    "\<And>A p. (copeland A p \<equiv> max_eliminator copeland_score A p)"
    by simp
  from max_cplscore_dcc copel_eq_max_copel
  show ?thesis
    unfolding defer_condorcet_consistency_def electoral_module_def
    by (smt (verit, ccfv_threshold))
qed

end
