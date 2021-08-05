theory Result_Rules
  imports "../Properties/Result_Properties"
          "../Components/Basic_Modules/Elect_Module"
          "../Components/Composites/Composite_Structures"
          Result_Facts

begin

theorem electing_imp_non_blocking:
  assumes electing: "electing m"
  shows "non_blocking m"
  using Diff_disjoint Diff_empty Int_absorb2 electing
        defer_in_alts elect_in_alts electing_def
        non_blocking_def reject_not_elec_or_def
  by (smt (verit, ccfv_SIG))

(*The sequential composition preserves the non-blocking property.*)
theorem seq_comp_presv_non_blocking[simp]:
  assumes
    non_blocking_m: "non_blocking m" and
    non_blocking_n: "non_blocking n"
  shows "non_blocking (m \<triangleright> n)"
proof -
  fix
    A :: "'a set" and
    p :: "'a Profile"
  let ?input_sound = "((A::'a set) \<noteq> {} \<and> finite_profile A p)"
  from non_blocking_m have
    "?input_sound \<longrightarrow> reject m A p \<noteq> A"
    by (simp add: non_blocking_def)
  with non_blocking_m have 0:
    "?input_sound \<longrightarrow> A - reject m A p \<noteq> {}"
    using Diff_eq_empty_iff non_blocking_def
          reject_in_alts subset_antisym
    by metis
  from non_blocking_m have
    "?input_sound \<longrightarrow> well_formed A (m A p)"
    by (simp add: electoral_module_def non_blocking_def)
  hence
    "?input_sound \<longrightarrow>
        elect m A p \<union> defer m A p = A - reject m A p"
    using non_blocking_def non_blocking_m elec_and_def_not_rej
    by metis
  with 0 have
    "?input_sound \<longrightarrow> elect m A p \<union> defer m A p \<noteq> {}"
    by auto
  hence "?input_sound \<longrightarrow> (elect m A p \<noteq> {} \<or> defer m A p \<noteq> {})"
    by simp
  with non_blocking_m non_blocking_n
  show ?thesis
    using Diff_empty Diff_subset_conv Un_empty fst_conv snd_conv
          defer_not_elec_or_rej elect_in_alts inf.absorb1 sup_bot_right
          non_blocking_def reject_in_alts sequential_composition.simps
          seq_comp_sound def_presv_fin_prof result_disj subset_antisym
    by (smt (verit))
qed

theorem elector_electing[simp]:
  assumes
    module_m: "electoral_module m" and
    non_block_m: "non_blocking m"
  shows "electing (elector m)"
proof -
  obtain
    AA :: "'a Electoral_Module \<Rightarrow> 'a set" and
    rrs :: "'a Electoral_Module \<Rightarrow> 'a Profile" where
    f1:
    "\<forall>f.
      (electing f \<or>
        {} = elect f (AA f) (rrs f) \<and> profile (AA f) (rrs f) \<and>
            finite (AA f) \<and> {} \<noteq> AA f \<or>
        \<not> electoral_module f) \<and>
            ((\<forall>A rs. {} \<noteq> elect f A rs \<or> \<not> profile A rs \<or>
                infinite A \<or> {} = A) \<and>
            electoral_module f \<or>
        \<not> electing f)"
    using electing_def
    by metis
  have non_block:
    "non_blocking
      (elect_module::'a set \<Rightarrow> _ Profile \<Rightarrow> _ Result)"
    by (simp add: electing_imp_non_blocking)
  thus ?thesis
    (* using f1 Diff_empty elect_module.elims elector.simps non_block_m
          non_blocking_def reject_not_elec_or_def seq_comp_defers_def_set
          seq_comp_presv_non_blocking snd_conv elect_mod_sound fst_conv
          elect_module.simps elector_sound module_m disjoint3.cases
          empty_iff ex_in_conv seq_comp_def_set_trans *)
  proof -
    obtain
      AAa :: "'a Electoral_Module \<Rightarrow> 'a set" and
      rrsa :: "'a Electoral_Module \<Rightarrow> 'a Profile" where
      f1:
      "\<forall>f.
        (electing f \<or>
          {} = elect f (AAa f) (rrsa f) \<and> profile (AAa f) (rrsa f) \<and>
              finite (AAa f) \<and> {} \<noteq> AAa f \<or>
        \<not> electoral_module f) \<and> ((\<forall>A rs. {} \<noteq> elect f A rs \<or>
        \<not> profile A rs \<or> infinite A \<or> {} = A) \<and> electoral_module f \<or>
        \<not> electing f)"
      using electing_def
      by metis
    obtain
      AAb :: "'a Result \<Rightarrow> 'a set" and
      AAc :: "'a Result \<Rightarrow> 'a set" and
      AAd :: "'a Result \<Rightarrow> 'a set" where
      f2:
      "\<forall>p. (AAb p, AAc p, AAd p) = p"
      using disjoint3.cases
      by (metis (no_types))
    have f3:
      "electoral_module (elector m)"
      using elector_sound module_m
      by simp
    have f4:
      "\<forall>p. (elect_r p, AAc p, AAd p) = p"
      using f2
      by simp
    have
      "finite (AAa (elector m)) \<and>
        profile (AAa (elector m)) (rrsa (elector m)) \<and>
        {} = elect (elector m) (AAa (elector m)) (rrsa (elector m)) \<and>
        {} = AAd (elector m (AAa (elector m)) (rrsa (elector m))) \<and>
        reject (elector m) (AAa (elector m)) (rrsa (elector m)) =
          AAc (elector m (AAa (elector m)) (rrsa (elector m))) \<longrightarrow>
              electing (elector m)"
      using f2 f1 Diff_empty elector.simps non_block_m snd_conv
            non_blocking_def reject_not_elec_or_def non_block
            seq_comp_presv_non_blocking
      by metis
    moreover
    {
      assume
        "{} \<noteq> AAd (elector m (AAa (elector m)) (rrsa (elector m)))"
      hence
        "\<not> profile (AAa (elector m)) (rrsa (elector m)) \<or>
          infinite (AAa (elector m))"
        using f4
        by simp
    }
    ultimately show ?thesis
      using f4 f3 f1 fst_conv snd_conv
      by metis
  qed
qed

(*
   Composing an electoral module that defers exactly 1 alternative
   in sequence after an electoral module that is electing
   results (still) in an electing electoral module.
*)
theorem seq_comp_electing[simp]:
  assumes def_one_m1:  "defers 1 m1" and
          electing_m2: "electing m2"
  shows "electing (m1 \<triangleright> m2)"
proof -
  have
    "\<forall>A p. (card A \<ge> 1 \<and> finite_profile A p) \<longrightarrow>
        card (defer m1 A p) = 1"
    using def_one_m1 defers_def
    by blast
  hence
    "\<forall>A p. (A \<noteq> {} \<and> finite_profile A p) \<longrightarrow>
        defer m1 A p \<noteq> {}"
    using One_nat_def Suc_leI card_eq_0_iff
          card_gt_0_iff zero_neq_one
    by metis
  thus ?thesis
    using Un_empty def_one_m1 defers_def electing_def
          electing_m2 seq_comp_def_then_elect_elec_set
          seq_comp_sound def_presv_fin_prof
    by (smt (verit, ccfv_threshold))
qed

(*
   Using a conservative aggregator, the parallel composition
   preserves the property non-electing.
*)
theorem conserv_agg_presv_non_electing[simp]:
  assumes
    non_electing_m: "non_electing m" and
    non_electing_n: "non_electing n" and
    conservative: "agg_conservative a"
  shows "non_electing (m \<parallel>\<^sub>a n)"
  unfolding non_electing_def
proof (safe)
  have emod_m: "electoral_module m"
    using non_electing_m
    by (simp add: non_electing_def)
  have emod_n: "electoral_module n"
    using non_electing_n
    by (simp add: non_electing_def)
  have agg_a: "aggregator a"
    using conservative
    by (simp add: agg_conservative_def)
  thus "electoral_module (m \<parallel>\<^sub>a n)"
    using emod_m emod_n agg_a par_comp_sound
    by simp
next
  fix
    A :: "'a set" and
    p :: "'a Profile" and
    x :: "'a"
  assume
    fin_A: "finite A" and
    prof_A: "profile A p" and
    x_wins: "x \<in> elect (m \<parallel>\<^sub>a n) A p"
  have emod_m: "electoral_module m"
    using non_electing_m
    by (simp add: non_electing_def)
  have emod_n: "electoral_module n"
    using non_electing_n
    by (simp add: non_electing_def)
  have
    "let c = (a A (m A p) (n A p)) in
      (elect_r c \<subseteq> ((elect m A p) \<union> (elect n A p)))"
    using conservative agg_conservative_def
          emod_m emod_n par_comp_result_sound
          combine_ele_rej_def fin_A prof_A
    by (smt (verit, ccfv_SIG))
  hence "x \<in> ((elect m A p) \<union> (elect n A p))"
    using x_wins
    by auto
  thus "x \<in> {}"
    using sup_bot_right non_electing_def fin_A
          non_electing_m non_electing_n prof_A
    by (metis (no_types, lifting))
qed

(*
   Using a conservative aggregator, the parallel composition
   preserves the property non-electing.
*)
theorem conserv_max_agg_presv_non_electing[simp]:
  assumes
    non_electing_m: "non_electing m" and
    non_electing_n: "non_electing n"
  shows "non_electing (m \<parallel>\<^sub>\<up> n)"
  using non_electing_m non_electing_n
  by simp

(*Sequential composition preserves the non-electing property.*)
theorem seq_comp_presv_non_electing[simp]:
  assumes
    "non_electing m" and
    "non_electing n"
  shows "non_electing (m \<triangleright> n)"
  using Un_empty assms non_electing_def prod.sel seq_comp_sound
        sequential_composition.simps def_presv_fin_prof
  by (smt (verit, del_insts))

lemma loop_comp_presv_non_electing_helper:
  assumes
    non_electing_m: "non_electing m" and
    f_prof: "finite_profile A p"
  shows
    "(n = card (defer acc A p) \<and> non_electing acc) \<Longrightarrow>
        elect (loop_comp_helper acc m t) A p = {}"
proof (induct n arbitrary: acc rule: less_induct)
  case(less n)
  thus ?case
    using loop_comp_helper.simps(1) loop_comp_helper.simps(2)
          non_electing_def non_electing_m f_prof psubset_card_mono
          seq_comp_presv_non_electing
    by (smt (verit, ccfv_threshold))
qed

(*The loop composition preserves the property non-electing.*)
theorem loop_comp_presv_non_electing[simp]:
  assumes non_electing_m: "non_electing m"
  shows "non_electing (m \<circlearrowleft>\<^sub>t)"
  unfolding non_electing_def
proof (safe, simp_all)
  show "electoral_module (m \<circlearrowleft>\<^sub>t)"
    using loop_comp_sound non_electing_def non_electing_m
    by metis
next
    fix
      A :: "'a set" and
      p :: "'a Profile" and
      x :: "'a"
    assume
      fin_A: "finite A" and
      prof_A: "profile A p" and
      x_elect: "x \<in> elect (m \<circlearrowleft>\<^sub>t) A p"
    show "False"
  using def_mod_non_electing loop_comp_presv_non_electing_helper
        non_electing_m empty_iff fin_A loop_comp_code
        non_electing_def prof_A x_elect
  by metis
qed

(*
   Revising an electing electoral module results in a
   non-blocking electoral module.
*)
theorem rev_comp_non_blocking[simp]:
  assumes "electing m"
  shows "non_blocking (m\<down>)"
  unfolding non_blocking_def
proof (safe, simp_all)
  show "electoral_module (m\<down>)"
    using assms electing_def rev_comp_sound
    by (metis (no_types, lifting))
next
  fix
    A :: "'a set" and
    p :: "'a Profile" and
    x :: "'a"
  assume
    fin_A: "finite A" and
    prof_A: "profile A p" and
    no_elect: "A - elect m A p = A" and
    x_in_A: "x \<in> A"
  from no_elect have non_elect:
    "non_electing m"
    using assms prof_A x_in_A fin_A electing_def empty_iff
          Diff_disjoint Int_absorb2 elect_in_alts
    by (metis (no_types, lifting))
  show "False"
    using non_elect assms electing_def empty_iff fin_A
          non_electing_def prof_A x_in_A
    by (metis (no_types, lifting))
qed

(*
   Composing a non-blocking, non-electing electoral module
   in sequence with an electoral module that defers exactly
   one alternative results in an electoral module that defers
   exactly one alternative.
*)
theorem seq_comp_def_one[simp]:
  assumes
    non_blocking_m: "non_blocking m" and
    non_electing_m: "non_electing m" and
    def_1_n: "defers 1 n"
  shows "defers 1 (m \<triangleright> n)"
  unfolding defers_def
proof (safe)
  have electoral_mod_m: "electoral_module m"
    using non_electing_m
    by (simp add: non_electing_def)
  have electoral_mod_n: "electoral_module n"
    using def_1_n
    by (simp add: defers_def)
  show "electoral_module (m \<triangleright> n)"
    using electoral_mod_m electoral_mod_n
    by simp
next
  fix
    A :: "'a set" and
    p :: "'a Profile"
  assume
    pos_card: "1 \<le> card A" and
    fin_A: "finite A" and
    prof_A: "profile A p"
  from pos_card have
    "A \<noteq> {}"
    by auto
  with fin_A prof_A have m_non_blocking:
    "reject m A p \<noteq> A"
    using non_blocking_m non_blocking_def
    by metis
  hence
    "\<exists>a. a \<in> A \<and> a \<notin> reject m A p"
    using pos_card non_electing_def non_electing_m
          reject_in_alts subset_antisym subset_iff
          fin_A prof_A subsetI
    by metis
  hence "defer m A p \<noteq> {}"
    using electoral_mod_defer_elem empty_iff pos_card
          non_electing_def non_electing_m fin_A prof_A
    by (metis (no_types))
  hence defer_non_empty:
    "card (defer m A p) \<ge> 1"
    using One_nat_def Suc_leI card_gt_0_iff pos_card fin_A prof_A
          non_blocking_def non_blocking_m def_presv_fin_prof
    by metis
  have defer_fun:
    "defer (m \<triangleright> n) A p =
      defer n (defer m A p) (limit_profile (defer m A p) p)"
    using def_1_n defers_def fin_A non_blocking_def non_blocking_m
          prof_A seq_comp_defers_def_set
    by (metis (no_types, hide_lams))
  have
    "\<forall>n f. defers n f =
      (electoral_module f \<and>
        (\<forall>A rs.
          (\<not> n \<le> card (A::'a set) \<or> infinite A \<or>
            \<not> profile A rs) \<or>
          card (defer f A rs) = n))"
    using defers_def
    by blast
  hence
    "card (defer n (defer m A p)
      (limit_profile (defer m A p) p)) = 1"
    using defer_non_empty def_1_n
          fin_A prof_A non_blocking_def
          non_blocking_m def_presv_fin_prof
    by metis
  thus "card (defer (m \<triangleright> n) A p) = 1"
    using defer_fun
    by auto
qed

lemma loop_comp_helper_iter_elim_def_n_helper:
  assumes
    non_electing_m: "non_electing m" and
    single_elimination: "eliminates 1 m" and
    terminate_if_n_left: "\<forall> r. ((t r) \<longleftrightarrow> (card (defer_r r) = x))" and
    x_greater_zero: "x > 0" and
    f_prof: "finite_profile A p"
  shows
    "(n = card (defer acc A p) \<and> n \<ge> x \<and> card (defer acc A p) > 1 \<and>
      non_electing acc) \<longrightarrow>
          card (defer (loop_comp_helper acc m t) A p) = x"
proof (induct n arbitrary: acc rule: less_induct)
  case(less n)
  have subset:
    "(card (defer acc A p) > 1 \<and> finite_profile A p \<and> electoral_module acc) \<longrightarrow>
        defer (acc \<triangleright> m) A p \<subset> defer acc A p"
    using seq_comp_elim_one_red_def_set single_elimination
    by blast
  hence step_reduces_defer_set:
    "(card (defer acc A p) > 1 \<and> finite_profile A p \<and> non_electing acc) \<longrightarrow>
        defer (acc \<triangleright> m) A p \<subset> defer acc A p"
    using non_electing_def
    by auto
  thus ?case
  proof cases
    assume term_satisfied: "t (acc A p)"
    have "card (defer_r (loop_comp_helper acc m t A p)) = x"
      using loop_comp_helper.simps(1) term_satisfied terminate_if_n_left
      by metis
    thus ?case
      by blast
  next
    assume term_not_satisfied: "\<not>(t (acc A p))"
    hence card_not_eq_x: "card (defer acc A p) \<noteq> x"
      by (simp add: terminate_if_n_left)
    have rec_step:
      "(card (defer acc A p) > 1 \<and> finite_profile A p \<and> non_electing acc) \<longrightarrow>
          loop_comp_helper acc m t A p =
              loop_comp_helper (acc \<triangleright> m) m t A p" (*needed for step*)
      using loop_comp_helper.simps(2) non_electing_def def_presv_fin_prof
            step_reduces_defer_set term_not_satisfied
      by metis
    thus ?case
    proof cases
      assume card_too_small: "card (defer acc A p) < x"
      thus ?thesis
        using not_le
        by blast
    next
      assume old_card_at_least_x: "\<not>(card (defer acc A p) < x)"
      obtain i where i_is_new_card: "i = card (defer (acc \<triangleright> m) A p)"
        by blast
      with card_not_eq_x have card_too_big:
        "card (defer acc A p) > x"
        using nat_neq_iff old_card_at_least_x
        by blast
      hence enough_leftover: "card (defer acc A p) > 1"
        using x_greater_zero
        by auto
      have "electoral_module acc \<longrightarrow> (defer acc A p) \<subseteq> A"
        by (simp add: defer_in_alts f_prof)
      hence step_profile:
        "electoral_module acc \<longrightarrow>
            finite_profile (defer acc A p)
              (limit_profile (defer acc A p) p)"
        using f_prof limit_profile_sound
        by auto
      hence
        "electoral_module acc \<longrightarrow>
            card (defer m (defer acc A p)
              (limit_profile (defer acc A p) p)) =
                card (defer acc A p) - 1"
        using non_electing_m single_elimination
              single_elim_decr_def_card2 enough_leftover
        by blast
      hence "electoral_module acc \<longrightarrow> i = card (defer acc A p) - 1"
        using sequential_composition.simps snd_conv i_is_new_card
        by metis
      hence "electoral_module acc \<longrightarrow> i \<ge> x"
        using card_too_big
        by linarith
      hence new_card_still_big_enough: "electoral_module acc \<longrightarrow> x \<le> i"
        by blast
      have
        "electoral_module acc \<and> electoral_module m \<longrightarrow>
            defer (acc \<triangleright> m) A p \<subseteq> defer acc A p"
        using enough_leftover f_prof subset
        by blast
      hence
        "electoral_module acc \<and> electoral_module m \<longrightarrow>
            i \<le> card (defer acc A p)"
        using card_mono i_is_new_card step_profile
        by blast
      hence i_geq_x:
        "electoral_module acc \<and> electoral_module m \<longrightarrow> (i = x \<or> i > x)"
        using nat_less_le new_card_still_big_enough
        by blast
      thus ?thesis
      proof cases
        assume new_card_greater_x: "electoral_module acc \<longrightarrow> i > x"
        hence "electoral_module acc \<longrightarrow> 1 < card (defer (acc \<triangleright> m) A p)"
          using x_greater_zero i_is_new_card
          by linarith
        moreover have new_card_still_big_enough2:
          "electoral_module acc \<longrightarrow> x \<le> i" (* Needed for step *)
          using i_is_new_card new_card_still_big_enough
          by blast
        moreover have
          "n = card (defer acc A p) \<longrightarrow>
              (electoral_module acc \<longrightarrow> i < n)" (* Needed for step *)
          using subset step_profile enough_leftover f_prof psubset_card_mono
                i_is_new_card
          by blast
        moreover have
          "electoral_module acc \<longrightarrow>
              electoral_module (acc \<triangleright> m)" (* Needed for step *)
          using non_electing_def non_electing_m seq_comp_sound
          by blast
        moreover have non_electing_new:
          "non_electing acc \<longrightarrow> non_electing (acc \<triangleright> m)"
          by (simp add: non_electing_m)
        ultimately have
          "(n = card (defer acc A p) \<and> non_electing acc \<and>
              electoral_module acc) \<longrightarrow>
                  card (defer (loop_comp_helper (acc \<triangleright> m) m t) A p) = x"
          using less.hyps i_is_new_card new_card_greater_x
          by blast
        thus ?thesis
          using f_prof rec_step non_electing_def
          by metis
      next
        assume i_not_gt_x: "\<not>(electoral_module acc \<longrightarrow> i > x)"
        hence "electoral_module acc \<and> electoral_module m \<longrightarrow> i = x"
          using i_geq_x
          by blast
        hence "electoral_module acc \<and> electoral_module m \<longrightarrow> t ((acc \<triangleright> m) A p)"
          using i_is_new_card terminate_if_n_left
          by blast
        hence
          "electoral_module acc \<and> electoral_module m \<longrightarrow>
              card (defer_r (loop_comp_helper (acc \<triangleright> m) m t A p)) = x"
          using loop_comp_helper.simps(1) terminate_if_n_left
          by metis
        thus ?thesis
          using i_not_gt_x dual_order.strict_iff_order i_is_new_card
                loop_comp_helper.simps(1) new_card_still_big_enough
                f_prof rec_step terminate_if_n_left
          by metis
      qed
    qed
  qed
qed

lemma loop_comp_helper_iter_elim_def_n:
  assumes
    non_electing_m: "non_electing m" and
    single_elimination: "eliminates 1 m" and
    terminate_if_n_left: "\<forall> r. ((t r) \<longleftrightarrow> (card (defer_r r) = x))" and
    x_greater_zero: "x > 0" and
    f_prof: "finite_profile A p" and
    acc_defers_enough: "card (defer acc A p) \<ge> x" and
    non_electing_acc: "non_electing acc"
  shows "card (defer (loop_comp_helper acc m t) A p) = x"
  using acc_defers_enough gr_implies_not0 le_neq_implies_less
        less_one linorder_neqE_nat loop_comp_helper.simps(1)
        loop_comp_helper_iter_elim_def_n_helper non_electing_acc
        non_electing_m f_prof single_elimination nat_neq_iff
        terminate_if_n_left x_greater_zero less_le
  by (metis (no_types, lifting))

lemma iter_elim_def_n_helper:
  assumes
    non_electing_m: "non_electing m" and
    single_elimination: "eliminates 1 m" and
    terminate_if_n_left: "\<forall> r. ((t r) \<longleftrightarrow> (card (defer_r r) = x))" and
    x_greater_zero: "x > 0" and
    f_prof: "finite_profile A p" and
    enough_alternatives: "card A \<ge> x"
  shows "card (defer (m \<circlearrowleft>\<^sub>t) A p) = x"
proof cases
  assume "card A = x"
  thus ?thesis
    by (simp add: terminate_if_n_left)
next
  assume card_not_x: "\<not> card A = x"
  thus ?thesis
  proof cases
    assume "card A < x"
    thus ?thesis
      using enough_alternatives not_le
      by blast
  next
    assume "\<not>card A < x"
    hence card_big_enough_A: "card A > x"
      using card_not_x
      by linarith
    hence card_m: "card (defer m A p) = card A - 1"
      using non_electing_m f_prof single_elimination
            single_elim_decr_def_card2 x_greater_zero
      by fastforce
    hence card_big_enough_m: "card (defer m A p) \<ge> x"
      using card_big_enough_A
      by linarith
    hence "(m \<circlearrowleft>\<^sub>t) A p = (loop_comp_helper m m t) A p"
      by (simp add: card_not_x terminate_if_n_left)
    thus ?thesis
      using card_big_enough_m non_electing_m f_prof single_elimination
            terminate_if_n_left x_greater_zero loop_comp_helper_iter_elim_def_n
      by metis
  qed
qed

theorem iter_elim_def_n[simp]:
  assumes
    non_electing_m: "non_electing m" and
    single_elimination: "eliminates 1 m" and
    terminate_if_n_left: "\<forall> r. ((t r) \<longleftrightarrow> (card (defer_r r) = n))" and
    x_greater_zero: "n > 0"
  shows "defers n (m \<circlearrowleft>\<^sub>t)"
proof -
  have
    "\<forall> A p. finite_profile A p \<and> card A \<ge> n \<longrightarrow>
        card (defer (m \<circlearrowleft>\<^sub>t) A p) = n"
    using iter_elim_def_n_helper non_electing_m single_elimination
          terminate_if_n_left x_greater_zero
    by blast
  moreover have "electoral_module (m \<circlearrowleft>\<^sub>t)"
    using loop_comp_sound eliminates_def single_elimination
    by blast
  thus ?thesis
    by (simp add: calculation defers_def)
qed

(*
   Using the max-aggregator for composing two compatible modules in parallel,
   whereof the first one is non-electing and defers exactly one alternative,
   and the second one rejects exactly two alternatives, the composition
   results in an electoral module that eliminates exactly one alternative.
*)
theorem par_comp_elim_one[simp]:
  assumes
    defers_m_1: "defers 1 m" and
    non_elec_m: "non_electing m" and
    rejec_n_2: "rejects 2 n" and
    disj_comp: "disjoint_compatibility m n"
  shows "eliminates 1 (m \<parallel>\<^sub>\<up> n)"
  unfolding eliminates_def
proof (safe)
  have electoral_mod_m: "electoral_module m"
    using non_elec_m
    by (simp add: non_electing_def)
  have electoral_mod_n: "electoral_module n"
    using rejec_n_2
    by (simp add: rejects_def)
  show "electoral_module (m \<parallel>\<^sub>\<up> n)"
    using electoral_mod_m electoral_mod_n
    by simp
next
  fix
    A :: "'a set" and
    p :: "'a Profile"
  assume
    min_2_card: "1 < card A" and
    fin_A: "finite A" and
    prof_A: "profile A p"
  have card_geq_1: "card A \<ge> 1"
    using min_2_card dual_order.strict_trans2 less_imp_le_nat
    by blast
  have module: "electoral_module m"
    using non_elec_m non_electing_def
    by auto
  have elec_card_0: "card (elect m A p) = 0"
    using fin_A prof_A non_elec_m card_eq_0_iff non_electing_def
    by metis
  moreover
  from card_geq_1 have def_card_1:
    "card (defer m A p) = 1"
    using defers_m_1 module fin_A prof_A
    by (simp add: defers_def)
  ultimately have card_reject_m:
    "card (reject m A p) = card A - 1"
  proof -
    have "finite A"
      by (simp add: fin_A)
    moreover have
      "well_formed A
        (elect m A p, reject m A p, defer m A p)"
      using fin_A prof_A electoral_module_def module
      by auto
    ultimately have
      "card A =
        card (elect m A p) + card (reject m A p) +
          card (defer m A p)"
      using result_count
      by blast
    thus ?thesis
      using def_card_1 elec_card_0
      by simp
  qed
  have case1: "card A \<ge> 2"
    using min_2_card
    by auto
  from case1 have card_reject_n:
    "card (reject n A p) = 2"
    using fin_A prof_A rejec_n_2 rejects_def
    by blast
  from card_reject_m card_reject_n
  have
    "card (reject m A p) + card (reject n A p) =
      card A + 1"
    using card_geq_1
    by linarith
  with disj_comp prof_A fin_A card_reject_m card_reject_n
  show
    "card (reject (m \<parallel>\<^sub>\<up> n) A p) = 1"
    using par_comp_rej_card
    by blast
qed

end