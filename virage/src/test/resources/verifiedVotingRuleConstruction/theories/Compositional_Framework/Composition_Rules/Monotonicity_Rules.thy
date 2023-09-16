theory Monotonicity_Rules
  imports "../Properties/Monotonicity_Properties"
          "../Properties/Disjoint_Compatibility"
          "../../Social_Choice_Properties/Weak_Monotonicity"
          "../Components/Compositional_Structures/Parallel_Composition"
          "../Components/Compositional_Structures/Sequential_Composition"
          "../Components/Basic_Modules/Maximum_Aggregator"
          Result_Rules
          Monotonicity_Facts

begin

(*
   Composing a defer-invariant-monotone electoral module in sequence before
   a non-electing, defer-monotone electoral module that defers exactly
   1 alternative results in a defer-lift-invariant electoral module.
*)
theorem def_inv_mono_imp_def_lift_inv[simp]:
  assumes
    strong_def_mon_m: "defer_invariant_monotonicity m" and
    non_electing_n: "non_electing n" and
    defers_1: "defers 1 n" and
    defer_monotone_n: "defer_monotonicity n"
  shows "defer_lift_invariance (m \<triangleright> n)"
  unfolding defer_lift_invariance_def
proof (safe)
  have electoral_mod_m: "electoral_module m"
    using defer_invariant_monotonicity_def
          strong_def_mon_m
    by auto
  have electoral_mod_n: "electoral_module n"
    using defers_1 defers_def
    by auto
  show "electoral_module (m \<triangleright> n)"
    using electoral_mod_m electoral_mod_n
    by simp
next
  fix
    A :: "'a set" and
    p :: "'a Profile" and
    q :: "'a Profile" and
    a :: "'a"
  assume
  defer_a_p: "a \<in> defer (m \<triangleright> n) A p" and
  lifted_a: "Profile.lifted A p q a"
  from strong_def_mon_m
  have non_electing_m: "non_electing m"
    by (simp add: defer_invariant_monotonicity_def)
  have electoral_mod_m: "electoral_module m"
    using strong_def_mon_m defer_invariant_monotonicity_def
    by auto
  have electoral_mod_n: "electoral_module n"
    using defers_1 defers_def
    by auto
  have finite_profile_q: "finite_profile A q"
    using lifted_a
    by (simp add: Profile.lifted_def)
  have finite_profile_p: "profile A p"
    using lifted_a
    by (simp add: Profile.lifted_def)
  show "(m \<triangleright> n) A p = (m \<triangleright> n) A q"
  proof cases
    assume not_unchanged: "defer m A q \<noteq> defer m A p"
    hence a_single_defer: "{a} = defer m A q"
      using strong_def_mon_m electoral_mod_n defer_a_p
            defer_invariant_monotonicity_def lifted_a
            seq_comp_def_set_trans finite_profile_p
            finite_profile_q
      by metis
    moreover have
      "{a} = defer m A q \<longrightarrow> defer (m \<triangleright> n) A q \<subseteq> {a}"
      using finite_profile_q electoral_mod_m electoral_mod_n
            seq_comp_def_set_sound
      by (metis (no_types, opaque_lifting))
    ultimately have
      "(a \<in> defer m A p) \<longrightarrow> defer (m \<triangleright> n) A q \<subseteq> {a}"
      by blast (* lifted defer-subset of a *)
    moreover have
      "(a \<in> defer m A p) \<longrightarrow> card (defer (m \<triangleright> n) A q) = 1"
      using One_nat_def a_single_defer card_eq_0_iff
            card_insert_disjoint defers_1 defers_def
            electoral_mod_m empty_iff finite.emptyI
            seq_comp_defers_def_set order_refl
            def_presv_fin_prof finite_profile_q
      by metis (* lifted defer set size 1 *)
    moreover have defer_a_in_m_p:
      "a \<in> defer m A p"
      using electoral_mod_m electoral_mod_n defer_a_p
            seq_comp_def_set_bounded finite_profile_p
            finite_profile_q
      by blast
    ultimately have
      "defer (m \<triangleright> n) A q = {a}" (* lifted defer set = a *)
      using Collect_mem_eq card_1_singletonE empty_Collect_eq
            insertCI subset_singletonD
      by metis
    moreover have
      "defer (m \<triangleright> n) A p = {a}" (* regular defer set = a *)
      using card_mono defers_def insert_subset Diff_insert_absorb
            seq_comp_def_set_bounded elect_in_alts non_electing_def
            non_electing_n defers_1 One_nat_def card_0_eq empty_iff
            card_1_singletonE card_Diff_singleton finite.emptyI
            card_insert_disjoint def_presv_fin_prof defer_a_p
            electoral_mod_m finite_Diff insertCI insert_Diff
            finite_profile_p finite_profile_q seq_comp_defers_def_set
      by (smt (verit))
    ultimately have (* defer sets equal *)
      "defer (m \<triangleright> n) A p = defer (m \<triangleright> n) A q"
      by blast
    moreover have (* elect sets sets equal *)
      "elect (m \<triangleright> n) A p = elect (m \<triangleright> n) A q"
      using finite_profile_p finite_profile_q
            non_electing_m non_electing_n
            seq_comp_presv_non_electing
            non_electing_def
      by metis (* elect sets equal *)
    thus ?thesis
      using calculation eq_def_and_elect_imp_eq
            electoral_mod_m electoral_mod_n
            finite_profile_p seq_comp_sound
            finite_profile_q
      by metis
  next
    assume not_different_alternatives:
      "\<not>(defer m A q \<noteq> defer m A p)"
    have "elect m A p = {}"
      using non_electing_m finite_profile_p finite_profile_q
      by (simp add: non_electing_def)
    moreover have "elect m A q = {}"
      using non_electing_m finite_profile_q
      by (simp add: non_electing_def)
    ultimately have elect_m_equal:
      "elect m A p = elect m A q"
      by simp (* m elects the same stuff *)
    from not_different_alternatives
    have same_alternatives: "defer m A q = defer m A p"
      by simp
    hence
      "(limit_profile (defer m A p) p) =
        (limit_profile (defer m A p) q) \<or>
          lifted (defer m A q)
            (limit_profile (defer m A p) p)
              (limit_profile (defer m A p) q) a"
      using defer_in_alts electoral_mod_m
            lifted_a finite_profile_q
            limit_prof_eq_or_lifted
      by metis
    thus ?thesis
    proof
      assume
        "limit_profile (defer m A p) p =
          limit_profile (defer m A p) q"
      hence same_profile:
        "limit_profile (defer m A p) p =
          limit_profile (defer m A q) q"
        using same_alternatives
        by simp
      hence results_equal_n:
        "n (defer m A q) (limit_profile (defer m A q) q) =
          n (defer m A p) (limit_profile (defer m A p) p)"
        by (simp add: same_alternatives)
      moreover have results_equal_m: "m A p = m A q"
        using elect_m_equal same_alternatives
              finite_profile_p finite_profile_q
        by (simp add: electoral_mod_m eq_def_and_elect_imp_eq)
      hence "(m \<triangleright> n) A p = (m \<triangleright> n) A q"
        using same_profile
        by auto
      thus ?thesis
        by blast
    next
      assume still_lifted:
        "lifted (defer m A q) (limit_profile (defer m A p) p)
          (limit_profile (defer m A p) q) a"
      hence a_in_def_p:
        "a \<in> defer n (defer m A p)
          (limit_profile (defer m A p) p)"
        using electoral_mod_m electoral_mod_n
              finite_profile_p defer_a_p
              seq_comp_def_set_trans
              finite_profile_q
        by metis
      hence a_still_deferred_p:
        "{a} \<subseteq> defer n (defer m A p)
          (limit_profile (defer m A p) p)"
        by simp
      have card_le_1_p: "card (defer m A p) \<ge> 1"
        using One_nat_def Suc_leI card_gt_0_iff
              electoral_mod_m electoral_mod_n
              equals0D finite_profile_p defer_a_p
              seq_comp_def_set_trans def_presv_fin_prof
              finite_profile_q
        by metis
      hence
        "card (defer n (defer m A p)
          (limit_profile (defer m A p) p)) = 1"
        using defers_1 defers_def electoral_mod_m
              finite_profile_p def_presv_fin_prof
              finite_profile_q
        by metis
      hence def_set_is_a_p:
        "{a} = defer n (defer m A p) (limit_profile (defer m A p) p)"
        using a_still_deferred_p card_1_singletonE
              insert_subset singletonD
        by metis
      have a_still_deferred_q:
        "a \<in> defer n (defer m A q)
          (limit_profile (defer m A p) q)"
        using still_lifted a_in_def_p
              defer_monotonicity_def
              defer_monotone_n electoral_mod_m
              same_alternatives
              def_presv_fin_prof finite_profile_q
        by metis
      have "card (defer m A q) \<ge> 1"
        using card_le_1_p same_alternatives
        by auto
      hence
        "card (defer n (defer m A q)
          (limit_profile (defer m A q) q)) = 1"
        using defers_1 defers_def electoral_mod_m
              finite_profile_q def_presv_fin_prof
        by metis
      hence def_set_is_a_q:
        "{a} =
          defer n (defer m A q)
            (limit_profile (defer m A q) q)"
        using a_still_deferred_q card_1_singletonE
              same_alternatives singletonD
        by metis
      have
        "defer n (defer m A p)
          (limit_profile (defer m A p) p) =
            defer n (defer m A q)
              (limit_profile (defer m A q) q)"
        using def_set_is_a_q def_set_is_a_p
        by auto
      thus ?thesis
        using seq_comp_presv_non_electing
              eq_def_and_elect_imp_eq non_electing_def
              finite_profile_p finite_profile_q
              non_electing_m non_electing_n
              seq_comp_defers_def_set
        by metis
    qed
  qed
qed

(*
   Using the max aggregator, composing two compatible
   electoral modules in parallel preserves defer-lift-invariance.
*)
theorem par_comp_def_lift_inv[simp]:
  assumes
    compatible: "disjoint_compatibility m n" and
    monotone_m: "defer_lift_invariance m" and
    monotone_n: "defer_lift_invariance n"
  shows "defer_lift_invariance (m \<parallel>\<^sub>\<up> n)"
  unfolding defer_lift_invariance_def
proof (safe)
  have electoral_mod_m: "electoral_module m"
    using monotone_m
    by (simp add: defer_lift_invariance_def)
  have electoral_mod_n: "electoral_module n"
    using monotone_n
    by (simp add: defer_lift_invariance_def)
  show "electoral_module (m \<parallel>\<^sub>\<up> n)"
    using electoral_mod_m electoral_mod_n
    by simp
next
  fix
    S :: "'a set" and
    p :: "'a Profile" and
    q :: "'a Profile" and
    x :: "'a"
  assume
    defer_x: "x \<in> defer (m \<parallel>\<^sub>\<up> n) S p" and
    lifted_x: "Profile.lifted S p q x"
  hence f_profs: "finite_profile S p \<and> finite_profile S q"
    by (simp add: lifted_def)
  from compatible obtain A::"'a set" where A:
    "A \<subseteq> S \<and> (\<forall>x \<in> A. indep_of_alt m S x \<and>
      (\<forall>p. finite_profile S p \<longrightarrow> x \<in> reject m S p)) \<and>
        (\<forall>x \<in> S-A. indep_of_alt n S x \<and>
      (\<forall>p. finite_profile S p \<longrightarrow> x \<in> reject n S p))"
    using disjoint_compatibility_def f_profs
    by (metis (no_types, lifting))
  have
    "\<forall>x \<in> S. prof_contains_result (m \<parallel>\<^sub>\<up> n) S p q x"
  proof cases
    assume a0: "x \<in> A"
    hence "x \<in> reject m S p"
      using A f_profs
      by blast
    with defer_x have defer_n: "x \<in> defer n S p"
      using compatible disjoint_compatibility_def
            mod_contains_result_def f_profs max_agg_rej4
      by metis
    have
      "\<forall>x \<in> A. mod_contains_result (m \<parallel>\<^sub>\<up> n) n S p x"
      using A compatible disjoint_compatibility_def
            max_agg_rej4 f_profs
      by metis
    moreover have "\<forall>x \<in> S. prof_contains_result n S p q x"
      using defer_n lifted_x prof_contains_result_def monotone_n f_profs
            defer_lift_invariance_def
      by (smt (verit, del_insts))
    moreover have
      "\<forall>x \<in> A. mod_contains_result n (m \<parallel>\<^sub>\<up> n) S q x"
      using A compatible disjoint_compatibility_def
            max_agg_rej3 f_profs
      by metis
    ultimately have 00:
      "\<forall>x \<in> A. prof_contains_result (m \<parallel>\<^sub>\<up> n) S p q x"
      by (simp add: mod_contains_result_def prof_contains_result_def)
    have
      "\<forall>x \<in> S-A. mod_contains_result (m \<parallel>\<^sub>\<up> n) m S p x"
      using A max_agg_rej2 monotone_m monotone_n f_profs
            defer_lift_invariance_def
      by metis
    moreover have "\<forall>x \<in> S. prof_contains_result m S p q x"
      using A lifted_x a0 prof_contains_result_def indep_of_alt_def
            lifted_imp_equiv_prof_except_a f_profs IntI
            electoral_mod_defer_elem empty_iff result_disj
      by (smt (verit, ccfv_threshold))
    moreover have
      "\<forall>x \<in> S-A. mod_contains_result m (m \<parallel>\<^sub>\<up> n) S q x"
      using A max_agg_rej1 monotone_m monotone_n f_profs
            defer_lift_invariance_def
      by metis
    ultimately have 01:
      "\<forall>x \<in> S-A. prof_contains_result (m \<parallel>\<^sub>\<up> n) S p q x"
      by (simp add: mod_contains_result_def prof_contains_result_def)
    from 00 01
    show ?thesis
      by blast
  next
    assume "x \<notin> A"
    hence a1: "x \<in> S-A"
      using DiffI lifted_x compatible f_profs
            Profile.lifted_def
      by (metis (no_types, lifting))
    hence "x \<in> reject n S p"
      using A f_profs
      by blast
    with defer_x have defer_n: "x \<in> defer m S p"
      using DiffD1 DiffD2 compatible dcompat_dec_by_one_mod
            defer_not_elec_or_rej disjoint_compatibility_def
            not_rej_imp_elec_or_def mod_contains_result_def
            max_agg_sound par_comp_sound f_profs
            maximum_parallel_composition.simps
      by metis
    have
      "\<forall>x \<in> A. mod_contains_result (m \<parallel>\<^sub>\<up> n) n S p x"
      using A compatible disjoint_compatibility_def
            max_agg_rej4 f_profs
      by metis
    moreover have "\<forall>x \<in> S. prof_contains_result n S p q x"
      using A lifted_x a1 prof_contains_result_def indep_of_alt_def
            lifted_imp_equiv_prof_except_a f_profs
            electoral_mod_defer_elem
      by (smt (verit, ccfv_threshold))
    moreover have
      "\<forall>x \<in> A. mod_contains_result n (m \<parallel>\<^sub>\<up> n) S q x"
      using A compatible disjoint_compatibility_def
            max_agg_rej3 f_profs
      by metis
    ultimately have 10:
      "\<forall>x \<in> A. prof_contains_result (m \<parallel>\<^sub>\<up> n) S p q x"
      by (simp add: mod_contains_result_def prof_contains_result_def)
    have
      "\<forall>x \<in> S-A. mod_contains_result (m \<parallel>\<^sub>\<up> n) m S p x"
      using A max_agg_rej2 monotone_m monotone_n
            f_profs defer_lift_invariance_def
      by metis
    moreover have "\<forall>x \<in> S. prof_contains_result m S p q x"
      using lifted_x defer_n prof_contains_result_def monotone_m
            f_profs defer_lift_invariance_def
      by (smt (verit, ccfv_threshold))
    moreover have
      "\<forall>x \<in> S-A. mod_contains_result m (m \<parallel>\<^sub>\<up> n) S q x"
      using A max_agg_rej1 monotone_m monotone_n
            f_profs defer_lift_invariance_def
      by metis
    ultimately have 11:
      "\<forall>x \<in> S-A. prof_contains_result (m \<parallel>\<^sub>\<up> n) S p q x"
      using electoral_mod_defer_elem
      by (simp add: mod_contains_result_def prof_contains_result_def)
    from 10 11
    show ?thesis
      by blast
  qed
  thus "(m \<parallel>\<^sub>\<up> n) S p = (m \<parallel>\<^sub>\<up> n) S q"
    using compatible disjoint_compatibility_def f_profs
          eq_alts_in_profs_imp_eq_results max_par_comp_sound
    by metis
qed

lemma def_lift_inv_seq_comp_help:
  assumes
    monotone_m: "defer_lift_invariance m" and
    monotone_n: "defer_lift_invariance n" and
    def_and_lifted: "a \<in> (defer (m \<triangleright> n) A p) \<and> lifted A p q a"
  shows "(m \<triangleright> n) A p = (m \<triangleright> n) A q"
proof -
  let ?new_Ap = "defer m A p"
  let ?new_Aq = "defer m A q"
  let ?new_p = "limit_profile ?new_Ap p"
  let ?new_q = "limit_profile ?new_Aq q"
  from monotone_m monotone_n have modules:
    "electoral_module m \<and> electoral_module n"
    by (simp add: defer_lift_invariance_def)
  hence "finite_profile A p \<longrightarrow> defer (m \<triangleright> n) A p \<subseteq> defer m A p"
    using seq_comp_def_set_bounded
    by metis
  moreover have profile_p: "lifted A p q a \<longrightarrow> finite_profile A p"
    by (simp add: lifted_def)
  ultimately have defer_subset: "defer (m \<triangleright> n) A p \<subseteq> defer m A p"
    using def_and_lifted
    by blast
  hence mono_m: "m A p = m A q"
    using monotone_m defer_lift_invariance_def def_and_lifted
          modules profile_p seq_comp_def_set_trans
    by metis
  hence new_A_eq: "?new_Ap = ?new_Aq"
    by presburger
  have defer_eq:
    "defer (m \<triangleright> n) A p = defer n ?new_Ap ?new_p"
    using sequential_composition.simps snd_conv
    by metis
  hence mono_n:
    "n ?new_Ap ?new_p = n ?new_Aq ?new_q"
  proof cases
    assume "lifted ?new_Ap ?new_p ?new_q a"
    thus ?thesis
      using defer_eq mono_m monotone_n
            defer_lift_invariance_def def_and_lifted
      by (metis (no_types, lifting))
  next
    assume a2: "\<not>lifted ?new_Ap ?new_p ?new_q a"
    from def_and_lifted have "finite_profile A q"
      by (simp add: lifted_def)
    with modules new_A_eq have 1:
      "finite_profile ?new_Ap ?new_q"
      using def_presv_fin_prof
      by (metis (no_types))
    moreover from modules profile_p def_and_lifted
    have 0:
      "finite_profile ?new_Ap ?new_p"
      using def_presv_fin_prof
      by (metis (no_types))
    moreover from defer_subset def_and_lifted
    have 2: "a \<in> ?new_Ap"
      by blast
    moreover from def_and_lifted have eql_lengths:
      "length ?new_p = length ?new_q"
      by (simp add: lifted_def)
    ultimately have 0:
      "(\<forall>i::nat. i < length ?new_p \<longrightarrow>
          \<not>Preference_Relation.lifted ?new_Ap (?new_p!i) (?new_q!i) a) \<or>
       (\<exists>i::nat. i < length ?new_p \<and>
          \<not>Preference_Relation.lifted ?new_Ap (?new_p!i) (?new_q!i) a \<and>
              (?new_p!i) \<noteq> (?new_q!i))"
      using a2 lifted_def
      by (metis (no_types, lifting))
    from def_and_lifted modules have
      "\<forall>i. (0 \<le> i \<and> i < length ?new_p) \<longrightarrow>
          (Preference_Relation.lifted A (p!i) (q!i) a \<or> (p!i) = (q!i))"
      using defer_in_alts Profile.lifted_def limit_prof_presv_size
      by metis
    with def_and_lifted modules mono_m have
      "\<forall>i. (0 \<le> i \<and> i < length ?new_p) \<longrightarrow>
          (Preference_Relation.lifted ?new_Ap (?new_p!i) (?new_q!i) a \<or>
           (?new_p!i) = (?new_q!i))"
      using limit_lifted_imp_eq_or_lifted defer_in_alts
            Profile.lifted_def limit_prof_presv_size
            limit_profile.simps nth_map
      by (metis (no_types, lifting))
    with 0 eql_lengths mono_m
    show ?thesis
      using leI not_less_zero nth_equalityI
      by metis
  qed
  from mono_m mono_n
  show ?thesis
    using sequential_composition.simps
    by (metis (full_types))
qed

(*Sequential composition preserves the property defer-lift-invariance.*)
theorem seq_comp_presv_def_lift_inv[simp]:
  assumes
    monotone_m: "defer_lift_invariance m" and
    monotone_n: "defer_lift_invariance n"
  shows "defer_lift_invariance (m \<triangleright> n)"
  using monotone_m monotone_n def_lift_inv_seq_comp_help
        seq_comp_sound defer_lift_invariance_def
  by (metis (full_types))

lemma loop_comp_helper_def_lift_inv_helper:
  assumes
    monotone_m: "defer_lift_invariance m" and
    f_prof: "finite_profile A p"
  shows
    "(defer_lift_invariance acc \<and> n = card (defer acc A p)) \<longrightarrow>
        (\<forall>q a.
          (a \<in> (defer (loop_comp_helper acc m t) A p) \<and>
            lifted A p q a) \<longrightarrow>
                (loop_comp_helper acc m t) A p =
                  (loop_comp_helper acc m t) A q)"
proof (induct n arbitrary: acc rule: less_induct)
  case (less n)
  have defer_card_comp:
    "defer_lift_invariance acc \<longrightarrow>
        (\<forall>q a. (a \<in> (defer (acc \<triangleright> m) A p) \<and> lifted A p q a) \<longrightarrow>
            card (defer (acc \<triangleright> m) A p) = card (defer (acc \<triangleright> m) A q))"
    using monotone_m def_lift_inv_seq_comp_help
    by metis
  have defer_card_acc:
    "defer_lift_invariance acc \<longrightarrow>
        (\<forall>q a. (a \<in> (defer (acc) A p) \<and> lifted A p q a) \<longrightarrow>
            card (defer (acc) A p) = card (defer (acc) A q))"
    by (simp add: defer_lift_invariance_def)
  hence defer_card_acc_2:
    "defer_lift_invariance acc \<longrightarrow>
        (\<forall>q a. (a \<in> (defer (acc \<triangleright> m) A p) \<and> lifted A p q a) \<longrightarrow>
            card (defer (acc) A p) = card (defer (acc) A q))"
    using monotone_m f_prof defer_lift_invariance_def seq_comp_def_set_trans
    by metis
  thus ?case
  proof cases
    assume card_unchanged: "card (defer (acc \<triangleright> m) A p) = card (defer acc A p)"
    with defer_card_comp defer_card_acc monotone_m
    have
      "defer_lift_invariance (acc) \<longrightarrow>
          (\<forall>q a. (a \<in> (defer (acc) A p) \<and> lifted A p q a) \<longrightarrow>
              (loop_comp_helper acc m t) A q = acc A q)"
      using card_subset_eq defer_in_alts less_irrefl
            loop_comp_helper.simps(1) f_prof psubset_card_mono
            sequential_composition.simps def_presv_fin_prof snd_conv
            defer_lift_invariance_def seq_comp_def_set_bounded
            loop_comp_code_helper
      by (smt (verit))
    moreover from card_unchanged have
      "(loop_comp_helper acc m t) A p = acc A p"
      using loop_comp_helper.simps(1) order.strict_iff_order
            psubset_card_mono
      by metis
    ultimately have
      "(defer_lift_invariance (acc \<triangleright> m) \<and> defer_lift_invariance acc) \<longrightarrow>
          (\<forall>q a. (a \<in> (defer (loop_comp_helper acc m t) A p) \<and>
              lifted A p q a) \<longrightarrow>
                  (loop_comp_helper acc m t) A p =
                    (loop_comp_helper acc m t) A q)"
      using defer_lift_invariance_def
      by metis
    thus ?thesis
      using monotone_m seq_comp_presv_def_lift_inv
      by blast
  next
    assume card_changed:
      "\<not> (card (defer (acc \<triangleright> m) A p) = card (defer acc A p))"
    with f_prof seq_comp_def_card_bounded have card_smaller_for_p:
      "electoral_module (acc) \<longrightarrow>
          (card (defer (acc \<triangleright> m) A p) < card (defer acc A p))"
      using monotone_m order.not_eq_order_implies_strict
            defer_lift_invariance_def
      by (metis (full_types))
    with defer_card_acc_2 defer_card_comp have card_changed_for_q:
      "defer_lift_invariance (acc) \<longrightarrow>
          (\<forall>q a. (a \<in> (defer (acc \<triangleright> m) A p) \<and> lifted A p q a) \<longrightarrow>
              (card (defer (acc \<triangleright> m) A q) < card (defer acc A q)))"
      using defer_lift_invariance_def
      by (metis (no_types, lifting))
    thus ?thesis
    proof cases
      assume t_not_satisfied_for_p: "\<not> t (acc A p)"
      hence t_not_satisfied_for_q:
        "defer_lift_invariance (acc) \<longrightarrow>
            (\<forall>q a. (a \<in> (defer (acc \<triangleright> m) A p) \<and> lifted A p q a) \<longrightarrow>
                \<not> t (acc A q))"
        using monotone_m f_prof defer_lift_invariance_def seq_comp_def_set_trans
        by metis
      from card_changed defer_card_comp defer_card_acc
      have
        "(defer_lift_invariance (acc \<triangleright> m) \<and> defer_lift_invariance (acc)) \<longrightarrow>
            (\<forall>q a. (a \<in> (defer (acc \<triangleright> m) A p) \<and> lifted A p q a) \<longrightarrow>
                card (defer (acc \<triangleright> m) A q) \<noteq> (card (defer acc A q)))"
      proof -
        have
          "\<forall>f. (defer_lift_invariance f \<or>
            (\<exists>A rs rsa a. f A rs \<noteq> f A rsa \<and>
              Profile.lifted A rs rsa (a::'a) \<and>
              a \<in> defer f A rs) \<or> \<not> electoral_module f) \<and>
              ((\<forall>A rs rsa a. f A rs = f A rsa \<or> \<not> Profile.lifted A rs rsa a \<or>
                  a \<notin> defer f A rs) \<and> electoral_module f \<or> \<not> defer_lift_invariance f)"
          using defer_lift_invariance_def
          by blast
        thus ?thesis
          using card_changed monotone_m f_prof seq_comp_def_set_trans
          by (metis (no_types, opaque_lifting))
      qed
      hence
        "defer_lift_invariance (acc \<triangleright> m) \<and> defer_lift_invariance (acc) \<longrightarrow>
            (\<forall>q a. (a \<in> (defer (acc \<triangleright> m) A p) \<and> lifted A p q a) \<longrightarrow>
                defer (acc \<triangleright> m) A q \<subset> defer acc A q)"
        using defer_card_acc defer_in_alts monotone_m prod.sel(2) f_prof
              psubsetI sequential_composition.simps def_presv_fin_prof
              defer_lift_invariance_def subsetCE Profile.lifted_def
              seq_comp_def_set_bounded
        by (smt (verit))
      with t_not_satisfied_for_p have rec_step_q:
        "(defer_lift_invariance (acc \<triangleright> m) \<and> defer_lift_invariance (acc)) \<longrightarrow>
            (\<forall>q a. (a \<in> (defer (acc \<triangleright> m) A p) \<and> lifted A p q a) \<longrightarrow>
                loop_comp_helper acc m t A q =
                  loop_comp_helper (acc \<triangleright> m) m t A q)"
        using defer_in_alts loop_comp_helper.simps(2) monotone_m subsetCE
              prod.sel(2) f_prof sequential_composition.simps card_eq_0_iff
              def_presv_fin_prof defer_lift_invariance_def card_changed_for_q
              gr_implies_not0 t_not_satisfied_for_q
        by (smt (verit, ccfv_SIG))
      have rec_step_p:
        "electoral_module acc \<longrightarrow>
            loop_comp_helper acc m t A p = loop_comp_helper (acc \<triangleright> m) m t A p"
        using card_changed defer_in_alts loop_comp_helper.simps(2)
              monotone_m prod.sel(2) f_prof psubsetI def_presv_fin_prof
              sequential_composition.simps defer_lift_invariance_def
              t_not_satisfied_for_p seq_comp_def_set_bounded
        by (smt (verit, best))
      thus ?thesis
        using card_smaller_for_p less.hyps
              loop_comp_helper_imp_no_def_incr monotone_m
              seq_comp_presv_def_lift_inv f_prof rec_step_q
              defer_lift_invariance_def subsetCE subset_eq
        by (smt (verit, ccfv_threshold))
    next
      assume t_satisfied_for_p: "\<not> \<not>t (acc A p)"
      thus ?thesis
        using loop_comp_helper.simps(1) defer_lift_invariance_def
        by metis
    qed
  qed
qed

lemma loop_comp_helper_def_lift_inv:
  assumes
    monotone_m: "defer_lift_invariance m" and
    monotone_acc: "defer_lift_invariance acc" and
    profile: "finite_profile A p"
  shows
    "\<forall>q a. (lifted A p q a \<and> a \<in> (defer (loop_comp_helper acc m t) A p)) \<longrightarrow>
        (loop_comp_helper acc m t) A p = (loop_comp_helper acc m t) A q"
  using loop_comp_helper_def_lift_inv_helper
        monotone_m monotone_acc profile
  by blast

lemma loop_comp_helper_def_lift_inv2:
  assumes
    monotone_m: "defer_lift_invariance m" and
    monotone_acc: "defer_lift_invariance acc"
  shows
    "\<forall>A p q a. (finite_profile A p \<and>
        lifted A p q a \<and>
        a \<in> (defer (loop_comp_helper acc m t) A p)) \<longrightarrow>
            (loop_comp_helper acc m t) A p = (loop_comp_helper acc m t) A q"
  using loop_comp_helper_def_lift_inv monotone_acc monotone_m
  by blast

lemma lifted_imp_fin_prof:
  assumes "lifted A p q a"
  shows "finite_profile A p"
  using assms Profile.lifted_def
  by fastforce

lemma loop_comp_helper_presv_def_lift_inv:
  assumes
    monotone_m: "defer_lift_invariance m" and
    monotone_acc: "defer_lift_invariance acc"
  shows "defer_lift_invariance (loop_comp_helper acc m t)"
proof -
  have
    "\<forall>f. (defer_lift_invariance f \<or>
         (\<exists>A rs rsa a. f A rs \<noteq> f A rsa \<and>
              Profile.lifted A rs rsa (a::'a) \<and>
              a \<in> defer f A rs) \<or>
         \<not> electoral_module f) \<and>
      ((\<forall>A rs rsa a. f A rs = f A rsa \<or> \<not> Profile.lifted A rs rsa a \<or>
          a \<notin> defer f A rs) \<and>
      electoral_module f \<or> \<not> defer_lift_invariance f)"
    using defer_lift_invariance_def
    by blast
  thus ?thesis
    using electoral_module_def lifted_imp_fin_prof
          loop_comp_helper_def_lift_inv loop_comp_helper_imp_partit
          monotone_acc monotone_m
    by (metis (full_types))
qed

(*The loop composition preserves defer-lift-invariance.*)
theorem loop_comp_presv_def_lift_inv[simp]:
  assumes monotone_m: "defer_lift_invariance m"
  shows "defer_lift_invariance (m \<circlearrowleft>\<^sub>t)"
proof -
  fix
    A :: "'a set"
  have
    "\<forall> p q a. (a \<in> (defer (m \<circlearrowleft>\<^sub>t) A p) \<and> lifted A p q a) \<longrightarrow>
        (m \<circlearrowleft>\<^sub>t) A p = (m \<circlearrowleft>\<^sub>t) A q"
    using defer_module.simps monotone_m lifted_imp_fin_prof
          loop_composition.simps(1) loop_composition.simps(2)
          loop_comp_helper_def_lift_inv2
    by (metis (full_types))
  thus ?thesis
    using def_mod_def_lift_inv monotone_m loop_composition.simps(1)
          loop_composition.simps(2) defer_lift_invariance_def
          loop_comp_sound loop_comp_helper_def_lift_inv2
          lifted_imp_fin_prof
    by (smt (verit, best))
qed

(*
   Revising an invariant monotone electoral module results in a
   defer-invariant-monotone electoral module.
*)
theorem rev_comp_def_inv_mono[simp]:
  assumes "invariant_monotonicity m"
  shows "defer_invariant_monotonicity (m\<down>)"
proof -
  have "\<forall>A p q w. (w \<in> defer (m\<down>) A p \<and> lifted A p q w) \<longrightarrow>
                  (defer (m\<down>) A q = defer (m\<down>) A p \<or> defer (m\<down>) A q = {w})"
    using assms
    by (simp add: invariant_monotonicity_def)
  moreover have "electoral_module (m\<down>)"
    using assms rev_comp_sound invariant_monotonicity_def
    by auto
  moreover have "non_electing (m\<down>)"
    using assms rev_comp_non_electing invariant_monotonicity_def
    by auto
  ultimately have "electoral_module (m\<down>) \<and> non_electing (m\<down>) \<and>
      (\<forall>A p q w. (w \<in> defer (m\<down>) A p \<and> lifted A p q w) \<longrightarrow>
                 (defer (m\<down>) A q = defer (m\<down>) A p \<or> defer (m\<down>) A q = {w}))"
    by blast
  thus ?thesis
    using defer_invariant_monotonicity_def
    by (simp add: defer_invariant_monotonicity_def)
qed

(*
   Every electoral module which is defer-lift-invariant is
   also defer-monotone.
*)
theorem dl_inv_imp_def_mono[simp]:
  assumes "defer_lift_invariance m"
  shows "defer_monotonicity m"
  using assms defer_monotonicity_def defer_lift_invariance_def
  by fastforce

(*
   Composing a defer-lift invariant and a non-electing
   electoral module that defers exactly one alternative
   in sequence with an electing electoral module
   results in a monotone electoral module.
*)
theorem seq_comp_mono[simp]:
  assumes
    def_monotone_m: "defer_lift_invariance m" and
    non_ele_m: "non_electing m" and
    def_one_m: "defers 1 m" and
    electing_n: "electing n"
  shows "monotonicity (m \<triangleright> n)"
  unfolding monotonicity_def
proof (safe)
  have electoral_mod_m: "electoral_module m"
    using non_ele_m
    by (simp add: non_electing_def)
  have electoral_mod_n: "electoral_module n"
    using electing_n
    by (simp add: electing_def)
  show "electoral_module (m \<triangleright> n)"
    using electoral_mod_m electoral_mod_n
    by simp
next
  fix
    A :: "'a set" and
    p :: "'a Profile" and
    q :: "'a Profile" and
    w :: "'a"
  assume
    fin_A: "finite A" and
    elect_w_in_p: "w \<in> elect (m \<triangleright> n) A p" and
    lifted_w: "Profile.lifted A p q w"
  have
    "finite_profile A p \<and> finite_profile A q"
    using lifted_w lifted_def
    by metis
  thus "w \<in> elect (m \<triangleright> n) A q"
    using seq_comp_def_then_elect defer_lift_invariance_def
          elect_w_in_p lifted_w def_monotone_m non_ele_m
          def_one_m electing_n
    by metis
qed

end