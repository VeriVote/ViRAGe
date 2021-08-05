theory Composite_Elimination_Modules
  imports "../Electoral_Module"
          "../Evaluation_Function"
          "../Basic_Modules/Elimination_Module"

begin

section \<open>Borda Module\<close>

text
\<open>This is the Borda module used by the Borda rule. The Borda rule is a voting
rule, where on each ballot, each alternative is assigned a score that depends
on how many alternatives are ranked below. The sum of all such scores for an
alternative is hence called their Borda score. The alternative with the highest
Borda score is elected. The module implemented herein only rejects the
alternatives not elected by the voting rule, and defers the alternatives that
would be elected by the full voting rule.\<close>

subsection \<open>Definition\<close>

fun borda_score :: "'a Evaluation_Function" where
  "borda_score x A p = (\<Sum>y \<in> A. (prefer_count p x y))"

fun borda :: "'a Electoral_Module" where
  "borda A p = max_eliminator borda_score A p"

section \<open>Condorcet Module\<close>

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

fun condorcet :: "'a Electoral_Module" where
  "condorcet A p = (max_eliminator condorcet_score) A p"

section \<open>Copeland Module\<close>

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

fun copeland :: "'a Electoral_Module" where
  "copeland A p = max_eliminator copeland_score A p"

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

section \<open>Minimax Module\<close>

text
\<open>This is the Minimax module used by the Minimax voting rule. The Minimax rule
elects the alternatives with the highest Minimax score. The module implemented
herein only rejects the alternatives not elected by the voting rule, and defers
the alternatives that would be elected by the full voting rule.\<close>

subsection \<open>Definition\<close>

fun minimax_score :: "'a Evaluation_Function" where
  "minimax_score x A p =
    Min {prefer_count p x y |y . y \<in> A-{x}}"

fun minimax :: "'a Electoral_Module" where
  "minimax A p = max_eliminator minimax_score A p"

subsection \<open>Lemma\<close>

lemma non_cond_winner_minimax_score:
  assumes
    prof: "profile A p" and
    winner: "condorcet_winner A p w" and
    l_in_A: "l \<in> A" and
    l_neq_w: "l \<noteq> w"
  shows "minimax_score l A p \<le> prefer_count p l w"
proof -
  let
    ?set = "{prefer_count p l y |y . y \<in> A-{l}}" and
      ?lscore = "minimax_score l A p"
  have "finite A"
    using prof condorcet_winner.simps winner
    by metis
  hence "finite (A-{l})"
    using finite_Diff
    by simp
  hence finite: "finite ?set"
    by simp
  have "w \<in> A"
    using condorcet_winner.simps winner
    by metis
  hence 0: "w \<in> A-{l}"
    using l_neq_w
    by force
  hence not_empty: "?set \<noteq> {}"
    by blast
  (*from 0 not_empty, have 10 "prefer_count p l w \<in> ?set"
     by blast*)
  have "?lscore = Min ?set"
    by simp
  hence 1: "?lscore \<in> ?set \<and> (\<forall>p \<in> ?set. ?lscore \<le> p)"
    using local.finite not_empty Min_le Min_eq_iff
    by (metis (no_types, lifting))
  thus ?thesis
    using "0"
    by auto
qed

end