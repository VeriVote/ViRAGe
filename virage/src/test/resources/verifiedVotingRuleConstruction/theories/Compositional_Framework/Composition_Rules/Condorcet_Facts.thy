theory Condorcet_Facts
  imports "../Properties/Condorcet_Properties"
          "../Components/Composites/Composite_Elimination_Modules"
          "../../Social_Choice_Properties/Condorcet_Consistency"
          Condorcet_Rules

begin

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
    by (metis (mono_tags, opaque_lifting))
  thus ?thesis
    using cond_winner_unique condorcet_score.simps zero_less_one
    by (metis (no_types))
qed

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

theorem minimax_score_cond_rating: "condorcet_rating minimax_score"
proof (unfold condorcet_rating_def minimax_score.simps prefer_count.simps, safe)
  fix
    A :: "'a set" and
    p :: "'a Profile" and
    w :: "'a" and
    l :: "'a"
  assume
    winner: "condorcet_winner A p w" and
    l_in_A: "l \<in> A" and
    l_neq_w:"l \<noteq> w"
  show
    "Min {card {i. i < length p \<and> (let r = (p!i) in (y \<preceq>\<^sub>r l))} |
        y. y \<in> A - {l}} <
      Min {card {i. i < length p \<and> (let r = (p!i) in (y \<preceq>\<^sub>r w))} |
          y. y \<in> A - {w}}"
  proof (rule ccontr)
    assume
      "\<not> Min {card {i. i < length p \<and> (let r = (p!i) in (y \<preceq>\<^sub>r l))} |
          y. y \<in> A - {l}} <
        Min {card {i. i < length p \<and> (let r = (p!i) in (y \<preceq>\<^sub>r w))} |
            y. y \<in> A - {w}}"
    hence
      "Min {card {i. i < length p \<and> (let r = (p!i) in (y \<preceq>\<^sub>r l))} |
          y. y \<in> A - {l}} \<ge>
        Min {card {i. i < length p \<and> (let r = (p!i) in (y \<preceq>\<^sub>r w))} |
            y. y \<in> A - {w}}"
      by linarith
    hence 000:
      "Min {prefer_count p l y |y . y \<in> A-{l}} \<ge>
        Min {prefer_count p w y |y . y \<in> A-{w}}"
      by auto
    have prof: "profile A p"
      using condorcet_winner.simps winner
      by metis
    from prof winner l_in_A l_neq_w
    have 100:
      "prefer_count p l w  \<ge> Min {prefer_count p l y |y . y \<in> A-{l}}"
      using non_cond_winner_minimax_score minimax_score.simps
      by metis
(*
    have l_in_A: "l \<in> A"
    using condorcet_winner_def winner
    by metis
    then l_neq_w have "w \<in> A-{l}" by blast
    hence 2: "{prefer_count p l y |y . y \<in> A-{l}} \<noteq> {}" by blast
    have "finite (A-{l})" using prof profile_def by auto
    hence 3: "finite {prefer_count p l y |y . y \<in> A-{l}}"
      by simp
    from 2 3
    have
      "\<exists> n \<in> A-{l} . prefer_count p l n =
        Min {prefer_count p l y |y . y \<in> A-{l}}"
      using Min_in by fastforce
    then obtain n where 4:
      "prefer_count p l n = Min {prefer_count p l y |y . y \<in> A-{l}}"
      by blast
*)
    from l_in_A
    have l_in_A_without_w: "l \<in> A-{w}"
      by (simp add: l_neq_w)
    hence 2: "{prefer_count p w y |y . y \<in> A-{w}} \<noteq> {}"
      by blast
    have "finite (A-{w})"
      using prof condorcet_winner.simps winner finite_Diff
      by metis
    hence 3: "finite {prefer_count p w y |y . y \<in> A-{w}}"
      by simp
    from 2 3
    have 4:
      "\<exists> n \<in> A-{w} . prefer_count p w n =
        Min {prefer_count p w y |y . y \<in> A-{w}}"
      using Min_in
      by fastforce
    then obtain n where 200:
      "prefer_count p w n =
        Min {prefer_count p w y |y . y \<in> A-{w}}" and
      6: "n \<in> A-{w}"
      by metis
    hence n_in_A: "n \<in> A"
      using DiffE
      by metis
    from 6
    have n_neq_w: "n \<noteq> w"
      by auto
    from winner
    have w_in_A: "w \<in> A"
      by simp
    from 6 prof winner
    have 300: "prefer_count p w n > prefer_count p n w"
      by simp
    from 100 000 200
    have 400: "prefer_count p l w \<ge> prefer_count p w n"
      by linarith
    with prof n_in_A w_in_A l_in_A n_neq_w
         l_neq_w pref_count_sym
    have 700: "prefer_count p n w \<ge> prefer_count p w l"
      by metis
    have "prefer_count p l w > prefer_count p w l"
      using "300" "400" "700"
      by linarith
    hence "wins l p w"
      by simp
    thus False
      using condorcet_winner.simps l_in_A_without_w
            wins_antisym winner
      by metis
  qed
qed

theorem minimax_is_dcc: "defer_condorcet_consistency minimax"
proof -
  have max_mmaxscore_dcc:
    "defer_condorcet_consistency (max_eliminator minimax_score)"
    using cr_eval_imp_dcc_max_elim
    by (simp add: minimax_score_cond_rating)
  have mmax_eq_max_mmax:
    "\<And>A p. (minimax A p \<equiv> max_eliminator minimax_score A p)"
    by simp
  from max_mmaxscore_dcc mmax_eq_max_mmax
  show ?thesis
    unfolding defer_condorcet_consistency_def electoral_module_def
    by (smt (verit, ccfv_threshold))
qed



end