theory minimax
  imports voting_rule_constructors eval_func electoral_modules elim_module condorcet_module borda_module
begin

(***************************************)
(*** Definition: Minimax Voting Rule ***)
(***************************************)

fun Minimax_score :: "'a Eval_function" where
  "Minimax_score x A p = Min{prefer_count p x y |y . y \<in> A-{x}}"

definition Minimax :: "'a Electoral_module" where
  "Minimax \<equiv> elector(MAX_Eliminator Minimax_score)"

(***************)
(*** Lemmata ***)
(***************)

lemma setcomprehension1 : "{ f x | x . x \<in> S } = f ` S" by auto

lemma setcomprehension2 :
shows "{ prefer_count p x y | y . y \<in> A-{x}} = (prefer_count p x) ` (A-{x})"
  by blast

lemma minimax_score_loser:
  assumes profile : "profile_on A p" and
  winner : "condorcet_winner_in A p w" and
  l_in_A : "l \<in> A" and
  l_neq_w: "l \<noteq> w"
shows "Minimax_score l A p \<le> prefer_count p l w"
proof -
  let ?set = "{prefer_count p l y |y . y \<in> A-{l}}" and ?lscore = "Minimax_score l A p"
  have "finite A" using profile profile_on_def by blast
  hence "finite (A-{l})" by blast
  hence finite : "finite ?set" by simp
  have "w \<in> A" by (meson condorcet_winner_in_def winner)
  hence 0: "w \<in> A-{l}" using l_neq_w by blast
  hence not_empty : "?set \<noteq> {}" by blast
  
  (* from 0 not_empty have 10 "prefer_count p l w \<in> ?set"
    by blast *)

  have "?lscore = Min ?set" by simp
  hence 1 : "?lscore \<in> ?set \<and> (\<forall>p \<in> ?set. ?lscore \<le> p)" using Min_in local.finite not_empty by auto
 
  thus ?thesis
    using "0" by blast
qed


lemma minimax_score_is_condorcet_rating:
  shows "condorcet_rating Minimax_score"
proof (unfold condorcet_rating_def, auto)
  fix A :: "'a set" and p :: "'a Profile" and w :: "'a"  and l::"'a"
  assume winner: "condorcet_winner_in A p w"
  and    l_in_A: "l \<in> A"
  and    l_neq_w:"l \<noteq> w"
  show "Min {card {i. i < length p \<and> y \<preceq>\<^sub>(p ! i) l} |y. y \<in> A \<and> y \<noteq> l}
       < Min {card {i. i < length p \<and> y \<preceq>\<^sub>(p ! i) w} |y. y \<in> A \<and> y \<noteq> w}"
  proof (rule ccontr)
    assume  " \<not> Min {card {i. i < length p \<and> y \<preceq>\<^sub>(p ! i) l} |y. y \<in> A \<and> y \<noteq> l}
       < Min {card {i. i < length p \<and> y \<preceq>\<^sub>(p ! i) w} |y. y \<in> A \<and> y \<noteq> w}"
    hence " Min {card {i. i < length p \<and> y \<preceq>\<^sub>(p ! i) l} |y. y \<in> A \<and> y \<noteq> l}
       \<ge> Min {card {i. i < length p \<and> y \<preceq>\<^sub>(p ! i) w} |y. y \<in> A \<and> y \<noteq> w}"
      by linarith 
    hence 000 :"Min{prefer_count p l y |y . y \<in> A-{l}} \<ge> Min{prefer_count p w y |y . y \<in> A-{w}}"
      by auto

    have profile : "profile_on A p" by (meson condorcet_winner_in_def winner)
    from profile winner l_in_A l_neq_w have 100 :"prefer_count p l w  \<ge> Min{prefer_count p l y |y . y \<in> A-{l}}"
      using minimax_score_loser by force

(*
    have l_in_A : "l \<in> A" by (meson condorcet_winner_in_def winner)
    from this l_neq_w have "w \<in> A-{l}" by blast

    hence 2 : "{prefer_count p l y |y . y \<in> A-{l}} \<noteq> {}" by blast

    have "finite (A-{l})" using profile profile_on_def by auto
    hence 3 :"finite {prefer_count p l y |y . y \<in> A-{l}}"
      by simp 
    
    from 2 3 have "\<exists> n \<in> A-{l} . prefer_count p l n = Min{prefer_count p l y |y . y \<in> A-{l}}"
      using Min_in by fastforce
    from this obtain n where 4: "prefer_count p l n = Min{prefer_count p l y |y . y \<in> A-{l}}" by blast
*)

    from l_in_A  have l_in_A_without_w : "l \<in> A-{w}" by (simp add: l_neq_w)
    hence 2 : "{prefer_count p w y |y . y \<in> A-{w}} \<noteq> {}" by blast
    have "finite (A-{w})" using profile profile_on_def by auto
    hence 3 :"finite {prefer_count p w y |y . y \<in> A-{w}}"
      by simp
    from 2 3 have 4 :"\<exists> n \<in> A-{w} . prefer_count p w n = Min{prefer_count p w y |y . y \<in> A-{w}}"
      using Min_in by fastforce
    from this obtain n  where 200: "prefer_count p w n = Min{prefer_count p w y |y . y \<in> A-{w}}" 
       and 6 : "n \<in> A-{w}" by blast
    hence n_in_A : "n \<in> A" by blast
    from 6 have n_neq_w : "n \<noteq> w" by blast
    
    from winner have w_in_A : "w \<in> A"
      by (simp add: condorcet_winner_in_def) 



    from 6 profile winner have 300 : "prefer_count p w n > prefer_count p n w "  by (simp add: condorcet_winner_in_def wins_def)
    from 100 000 200 have 400 : "prefer_count p l w \<ge> prefer_count p w n" by linarith
    from this profile n_in_A w_in_A l_in_A n_neq_w l_neq_w prefer_count_symmetry have 700 : "prefer_count p n w \<ge> prefer_count p w l"
      by fastforce
    
    have "prefer_count p l w > prefer_count p w l"
      using "300" "400" "700" by linarith
    hence "wins l p w"
      by (simp add: wins_def)

    thus False
      by (meson condorcet_winner_in_def l_in_A_without_w only_one_can_win winner) 
  qed
qed

corollary minimax_module_is_cc:
  shows "condorcet_consistent Minimax"
proof -
  have "\<not> defer_condorcet_consistent (\<lambda>A. MAX_Eliminator Minimax_score (A::'a set)) \<or> condorcet_consistent (Minimax::'a set \<Rightarrow> (_ \<times> _) set list \<Rightarrow> _ set \<times> _ set \<times> _ set)"
    by (simp add: Minimax_def m_defer_cc_implies_elector_m_cc)
  then show ?thesis
    using minimax_score_is_condorcet_rating cr_eval_implies_max_elim_is_def_cc by blast
qed

end