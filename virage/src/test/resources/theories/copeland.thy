theory copeland
  imports voting_rule_constructors eval_func electoral_modules elim_module condorcet_module
begin

(****************************************)
(*** Definition: Copeland Voting Rule ***)
(****************************************)

fun Copeland_score :: "'a Eval_function" where
  "Copeland_score x A p = card{y \<in> A . wins x p y} - card{y \<in> A . wins y p x} "

definition Copeland :: "'a Electoral_module" where
  "Copeland \<equiv> elector(MAX_Eliminator Copeland_score)"

(***************)
(*** Lemmata ***)
(***************)

(* Für einen Condorcet-Winner w gilt: card{y \<in> A . wins x p y} = |A|-1 *)
lemma condorcet_winner_number_of_wins:
  assumes winner : "condorcet_winner_in A p w"
  shows "card{y \<in> A . wins w p y} = card A -1"
proof -
  from winner have 0 : "\<forall>x \<in> A - {w} . wins w p x" by (simp add: condorcet_winner_in_def)
  have 1 : "\<forall>M . {x \<in> M . True} = M" by blast
  from 0 1 have "{x \<in> A - {w} . wins w p x} = A - {w}" by blast 
  then have 10 : "card {x \<in> A - {w} . wins w p x} = card (A - {w})" by simp
  from winner have 11 : "w \<in> A" by (simp add: condorcet_winner_in_def) 
  then have  "card (A - {w}) = card A - 1" by (meson card_Diff_singleton condorcet_winner_in_def winner)
  then have amount1 : "card {x \<in> A - {w} . wins w p x} = card (A) - 1" using "10" by linarith 
  
  have 2 : "\<forall>x \<in> {w} . \<not> wins x p x" by (simp add: one_cant_win_against_himself)
  have 3 : "\<forall>M . {x \<in> M . False} = {}" by blast
  from 2 3 have "{x \<in> {w} . wins w p x} = {}" by blast
  then have amount2 : "card {x \<in> {w} . wins w p x} = 0" by simp

  have disjunct : "{x \<in> A - {w} . wins w p x} \<inter> {x \<in> {w} . wins w p x} = {}" by blast

  have union : "{x \<in> A - {w} . wins w p x} \<union> {x \<in> {w} . wins w p x} = {x \<in> A . wins w p x}"  using "2" by blast 

  have finiteness1 : "finite {x \<in> A - {w} . wins w p x}" using condorcet_winner_in_def winner by fastforce
  have finiteness2 : "finite {x \<in> {w} . wins w p x}" by simp 

  from finiteness1 finiteness2 disjunct card_Un_disjoint have
      "card ({x \<in> A - {w} . wins w p x} \<union> {x \<in> {w} . wins w p x}) = card {x \<in> A - {w} . wins w p x} + card {x \<in> {w} . wins w p x}"
    by blast

  from this union have "card {x \<in> A . wins w p x} = card {x \<in> A - {w} . wins w p x} + card {x \<in> {w} . wins w p x}"
    by simp

  from this amount1 amount2 show ?thesis by linarith
qed

(* Für einen Condorcet-Winner w gilt: card{y \<in> A . wins y p x} = 0 *)
lemma condorcet_winner_number_of_loss:
  assumes winner : "condorcet_winner_in A p w"
  shows "card{y \<in> A . wins y p w} = 0" by (metis (no_types, lifting) Collect_empty_eq card_0_eq card_infinite condorcet_winner_in_def insert_Diff insert_iff only_one_can_win winner)

(* Copeland Score of a Condorcet Winner *)
lemma condorcet_winner_copeland_score:
  assumes winner : "condorcet_winner_in A p w"
  shows "Copeland_score w A p = card A -1"
proof (auto)
  show "card {y \<in> A. wins w p y} - card {y \<in> A. wins y p w} = card A - Suc 0"
    by (simp add: condorcet_winner_number_of_loss condorcet_winner_number_of_wins winner)
qed

(* Für einen Nicht-Condorcet-Winner l gilt: card{y \<in> A . wins x p y} <= |A|-1 -1 *)
lemma non_condorcet_winner_number_of_wins:
  assumes winner : "condorcet_winner_in A p w" and
          loser : "l \<noteq> w" and
          l_in_A : "l \<in> A"
        shows "card{y \<in> A . wins l p y} <= card A - 2 "
proof -
  from winner loser l_in_A have "wins w p l" by (simp add: condorcet_winner_in_def)
  hence 0 : "\<not> wins l p w" by (simp add: only_one_can_win)
  have 1 : "\<not> wins l p l" by (simp add: one_cant_win_against_himself)
  from 0 1 have 2: "{y \<in> A . wins l p y} = {y \<in> A-{l,w} . wins l p y}" by blast

  have 3 : "\<forall> M f . finite M \<longrightarrow> card {x \<in> M . f x} \<le> card M" by (simp add: card_mono) 
  have 4 : "finite (A-{l,w})" by (meson condorcet_winner_in_def finite_Diff winner)
  from 3 4 have 5 : " card {y \<in> A-{l,w} . wins l p y} \<le> card (A-{l,w})" by (metis (full_types)) 

  have "w \<in> A" by (meson condorcet_winner_in_def winner)
  from this l_in_A have "card(A-{l,w}) = card A - card {l,w}" by (simp add: card_Diff_subset)
  from this have "card(A-{l,w}) = card A - 2" by (simp add: loser)
  
  from this 5 2 show ?thesis by simp
qed

(* Copeland_score is condorcet rating *)
lemma copeland_score_is_condorcet_rating:
  shows "condorcet_rating Copeland_score"
proof (unfold condorcet_rating_def, auto)
  fix A :: "'a set" and p :: "'a Profile" and w l
  assume winner : "condorcet_winner_in A p w" and
         l_in_A : "l \<in> A" and 
         l_neq_w: "l \<noteq> w"
  show "card {y \<in> A. wins l p y} - card {y \<in> A. wins y p l}
       < card {y \<in> A. wins w p y} - card {y \<in> A. wins y p w}"
  proof -
    from winner have 0 : "card {y \<in> A. wins w p y} - card {y \<in> A. wins y p w} = card A -1"
      using condorcet_winner_copeland_score by fastforce

    from winner l_neq_w l_in_A have 1 : "card {y \<in> A. wins l p y} - card {y \<in> A. wins y p l} \<le> card A -2"
      using non_condorcet_winner_number_of_wins by fastforce

    have 2 :"card A -2 < card A -1" by (metis card_0_eq card_Diff_singleton condorcet_winner_in_def diff_less_mono2 empty_iff finite_Diff insertE insert_Diff l_in_A l_neq_w neq0_conv one_less_numeral_iff semiring_norm(76) winner zero_less_diff)

    from this have "card {y \<in> A. wins l p y} - card {y \<in> A. wins y p l} < card A -1"
      using "1" le_less_trans by blast

    from this 0 show ?thesis
      by linarith
  qed
qed

corollary compeland_module_is_cc:
  shows "condorcet_consistent Copeland"
proof -
  have "\<not> defer_condorcet_consistent (\<lambda>A. MAX_Eliminator Copeland_score (A::'a set)) \<or> condorcet_consistent (Copeland::'a set \<Rightarrow> (_ \<times> _) set list \<Rightarrow> _ set \<times> _ set \<times> _ set)"
    by (simp add: Copeland_def m_defer_cc_implies_elector_m_cc)
  then show ?thesis
    using copeland_score_is_condorcet_rating cr_eval_implies_max_elim_is_def_cc by blast
qed



end