(*  File:       Sequential_Composition.thy
    Copyright   2021  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Karsten Diekhoff, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Jonas Kraemer, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Michael Kirsten, Karlsruhe Institute of Technology (KIT)"\<close>

section \<open>Sequential Composition\<close>

theory Sequential_Composition
  imports "../Electoral_Module"
          "../../Properties/Result_Properties"

begin

text
\<open>The sequential composition creates a new electoral module from
two electoral modules. In a sequential composition, the second
electoral module makes decisions over alternatives deferred by
the first electoral module.\<close>

subsection \<open>Definition\<close>

fun sequential_composition :: "'a Electoral_Module \<Rightarrow> 'a Electoral_Module \<Rightarrow>
        'a Electoral_Module" where
  "sequential_composition m n A p =
    (let new_A = defer m A p;
        new_p = limit_profile new_A p in (
                  (elect m A p) \<union> (elect n new_A new_p),
                  (reject m A p) \<union> (reject n new_A new_p),
                  defer n new_A new_p))"

abbreviation sequence ::
  "'a Electoral_Module \<Rightarrow> 'a Electoral_Module \<Rightarrow> 'a Electoral_Module"
     (infix "\<triangleright>" 50) where
  "m \<triangleright> n == sequential_composition m n"

lemma seq_comp_presv_disj:
  assumes module_m: "electoral_module m" and
          module_n: "electoral_module n" and
          f_prof:  "finite_profile A p"
  shows "disjoint3 ((m \<triangleright> n) A p)"
proof -
  let ?new_A = "defer m A p"
  let ?new_p = "limit_profile ?new_A p"
  from module_m f_prof have disjoint_m: "disjoint3 (m A p)"
    using electoral_module_def well_formed.simps
    by blast
  from module_m module_n def_presv_fin_prof f_prof have disjoint_n:
    "(disjoint3 (n ?new_A ?new_p))"
    using electoral_module_def well_formed.simps
    by metis
  with disjoint_m module_m module_n f_prof have 0:
    "(elect m A p \<inter> reject n ?new_A ?new_p) = {}"
    using disjoint_iff_not_equal reject_in_alts
          def_presv_fin_prof result_disj subset_eq
    by (smt (verit, best))
  from disjoint_m disjoint_n def_presv_fin_prof f_prof
       module_m module_n have 1:
    "(elect m A p \<inter> defer n ?new_A ?new_p) = {}"
    using defer_in_alts disjoint_iff_not_equal
          rev_subsetD result_disj distrib_imp2
          Int_Un_distrib inf_sup_distrib1
          result_presv_alts sup_bot.left_neutral
          sup_bot.neutr_eq_iff sup_bot_right "0"
    by (smt (verit, del_insts))
  from disjoint_m disjoint_n def_presv_fin_prof f_prof
       module_m module_n have 2:
    "(reject m A p \<inter> reject n ?new_A ?new_p) = {}"
    using disjoint_iff_not_equal reject_in_alts
          set_rev_mp result_disj Int_Un_distrib2
          Un_Diff_Int boolean_algebra_cancel.inf2
          inf.order_iff inf_sup_aci(1) subsetD
    by (smt (verit, ccfv_threshold))
  from disjoint_m disjoint_n def_presv_fin_prof f_prof
       module_m module_n have 3:
    "(reject m A p \<inter> elect n ?new_A ?new_p) = {}"
    using disjoint_iff_not_equal elect_in_alts set_rev_mp
          result_disj Int_commute boolean_algebra_cancel.inf2
          defer_not_elec_or_rej inf.commute inf.orderE inf_commute
    by (smt (verit, ccfv_threshold))
  from 0 1 2 3 disjoint_m disjoint_n module_m module_n f_prof have
    "(elect m A p \<union> elect n ?new_A ?new_p) \<inter>
          (reject m A p \<union> reject n ?new_A ?new_p) = {}"
    using inf_sup_aci(1) inf_sup_distrib2 def_presv_fin_prof
          result_disj sup_inf_absorb sup_inf_distrib1
          distrib(3) sup_eq_bot_iff
    by (smt (verit, ccfv_threshold))
  moreover from 0 1 2 3 disjoint_n module_m module_n f_prof have
    "(elect m A p \<union> elect n ?new_A ?new_p) \<inter>
          (defer n ?new_A ?new_p) = {}"
    using Int_Un_distrib2 Un_empty def_presv_fin_prof result_disj
    by metis
  moreover from 0 1 2 3 f_prof disjoint_m disjoint_n module_m module_n
  have
    "(reject m A p \<union> reject n ?new_A ?new_p) \<inter>
          (defer n ?new_A ?new_p) = {}"
    using Int_Un_distrib2 defer_in_alts distrib_imp2
          def_presv_fin_prof result_disj subset_Un_eq
          sup_inf_distrib1
    by (smt (verit))
  ultimately have
    "disjoint3 (elect m A p \<union> elect n ?new_A ?new_p,
                reject m A p \<union> reject n ?new_A ?new_p,
                defer n ?new_A ?new_p)"
    by simp
  thus ?thesis
    using sequential_composition.simps
    by metis
qed

lemma seq_comp_presv_alts:
  assumes module_m: "electoral_module m" and
          module_n: "electoral_module n" and
          f_prof:  "finite_profile A p"
  shows "set_equals_partition A ((m \<triangleright> n) A p)"
proof -
  let ?new_A = "defer m A p"
  let ?new_p = "limit_profile ?new_A p"
  from module_m f_prof have "set_equals_partition A (m A p)"
    by (simp add: electoral_module_def)
  with module_m f_prof have 0:
    "elect m A p \<union> reject m A p \<union> ?new_A = A"
    by (simp add: result_presv_alts)
  from module_n def_presv_fin_prof f_prof module_m have
    "set_equals_partition ?new_A (n ?new_A ?new_p)"
    using electoral_module_def well_formed.simps
    by metis
  with module_m module_n f_prof have 1:
    "elect n ?new_A ?new_p \<union>
        reject n ?new_A ?new_p \<union>
        defer n ?new_A ?new_p = ?new_A"
    using def_presv_fin_prof result_presv_alts
    by metis
  from 0 1 have
    "(elect m A p \<union> elect n ?new_A ?new_p) \<union>
        (reject m A p \<union> reject n ?new_A ?new_p) \<union>
         defer n ?new_A ?new_p = A"
    by blast
  hence
    "set_equals_partition A
      (elect m A p \<union> elect n ?new_A ?new_p,
      reject m A p \<union> reject n ?new_A ?new_p,
      defer n ?new_A ?new_p)"
    by simp
  thus ?thesis
    using sequential_composition.simps
    by metis
qed

subsection \<open>Soundness\<close>

theorem seq_comp_sound[simp]:
  assumes module_m: "electoral_module m" and
          module_n: "electoral_module n"
        shows "electoral_module (m \<triangleright> n)"
  unfolding electoral_module_def
proof (safe)
  fix
    A :: "'a set" and
    p :: "'a Profile"
  assume
    fin_A: "finite A" and
    prof_A: "profile A p"
  have "\<forall>r. well_formed (A::'a set) r =
          (disjoint3 r \<and> set_equals_partition A r)"
    by simp
  thus "well_formed A ((m \<triangleright> n) A p)"
    using module_m module_n seq_comp_presv_disj
          seq_comp_presv_alts fin_A prof_A
    by metis
qed

subsection \<open>Lemmata\<close>

lemma seq_comp_dec_only_def:
  assumes
    module_m: "electoral_module m" and
    module_n: "electoral_module n" and
    f_prof: "finite_profile A p" and
    empty_defer: "defer m A p = {}"
  shows "(m \<triangleright> n) A p =  m A p"
  using Int_lower1 Un_absorb2 bot.extremum_uniqueI defer_in_alts
        elect_in_alts empty_defer module_m module_n prod.collapse
        f_prof reject_in_alts sequential_composition.simps
        def_presv_fin_prof result_disj
  by (smt (verit))

lemma seq_comp_def_then_elect:
  assumes
    n_electing_m: "non_electing m" and
    def_one_m: "defers 1 m" and
    electing_n: "electing n" and
    f_prof: "finite_profile A p"
  shows "elect (m \<triangleright> n) A p = defer m A p"
proof cases
  assume "A = {}"
  with electing_n n_electing_m f_prof show ?thesis
    using bot.extremum_uniqueI defer_in_alts elect_in_alts
          electing_def non_electing_def seq_comp_sound
    by metis
next
  assume assm: "A \<noteq> {}"
  from n_electing_m f_prof have ele: "elect m A p = {}"
    using non_electing_def
    by auto
  from assm def_one_m f_prof finite have def_card:
    "card (defer m A p) = 1"
    by (simp add: Suc_leI card_gt_0_iff defers_def)
  with n_electing_m f_prof have def:
    "\<exists>a \<in> A. defer m A p = {a}"
    using card_1_singletonE defer_in_alts
          non_electing_def singletonI subsetCE
    by metis
  from ele def n_electing_m have rej:
    "\<exists>a \<in> A. reject m A p = A-{a}"
    using Diff_empty def_one_m defers_def f_prof reject_not_elec_or_def
    by metis
  from ele rej def n_electing_m f_prof have res_m:
    "\<exists>a \<in> A. m A p = ({}, A-{a}, {a})"
    using Diff_empty combine_ele_rej_def non_electing_def
          reject_not_elec_or_def
    by metis
  hence
    "\<exists>a \<in> A. elect (m \<triangleright> n) A p =
        elect n {a} (limit_profile {a} p)"
    using prod.sel(1) prod.sel(2) sequential_composition.simps
          sup_bot.left_neutral
    by metis
  with def_card def electing_n n_electing_m f_prof have
    "\<exists>a \<in> A. elect (m \<triangleright> n) A p = {a}"
    using electing_for_only_alt non_electing_def prod.sel
          sequential_composition.simps def_presv_fin_prof
          sup_bot.left_neutral
    by metis
  with def def_card electing_n n_electing_m f_prof res_m
  show ?thesis
    using Diff_disjoint Diff_insert_absorb Int_insert_right
          Un_Diff_Int electing_for_only_alt empty_iff
          non_electing_def prod.sel sequential_composition.simps
          def_presv_fin_prof singletonI f_prof
    by (smt (verit, best))
qed

lemma seq_comp_def_card_bounded:
  assumes
    module_m: "electoral_module m" and
    module_n: "electoral_module n" and
    f_prof: "finite_profile A p"
  shows "card (defer (m \<triangleright> n) A p) \<le> card (defer m A p)"
  using card_mono defer_in_alts module_m module_n f_prof
        sequential_composition.simps def_presv_fin_prof snd_conv
  by metis

lemma seq_comp_def_set_bounded:
  assumes
    module_m: "electoral_module m" and
    module_n: "electoral_module n" and
    f_prof: "finite_profile A p"
  shows "defer (m \<triangleright> n) A p \<subseteq> defer m A p"
  using defer_in_alts module_m module_n prod.sel(2) f_prof
        sequential_composition.simps def_presv_fin_prof
  by metis

lemma seq_comp_defers_def_set:
  assumes
    module_m: "electoral_module m" and
    module_n: "electoral_module n" and
    f_prof: "finite_profile A p"
  shows
    "defer (m \<triangleright> n) A p =
      defer n (defer m A p) (limit_profile (defer m A p) p)"
  using sequential_composition.simps snd_conv
  by metis

lemma seq_comp_def_then_elect_elec_set:
  assumes
    module_m: "electoral_module m" and
    module_n: "electoral_module n" and
    f_prof: "finite_profile A p"
  shows
    "elect (m \<triangleright> n) A p =
      elect n (defer m A p) (limit_profile (defer m A p) p) \<union>
      (elect m A p)"
  using Un_commute fst_conv sequential_composition.simps
  by metis

lemma seq_comp_elim_one_red_def_set:
  assumes
    module_m: "electoral_module m" and
    module_n: "eliminates 1 n" and
    f_prof: "finite_profile A p" and
    enough_leftover: "card (defer m A p) > 1"
  shows "defer (m \<triangleright> n) A p \<subset> defer m A p"
  using enough_leftover module_m module_n f_prof
        sequential_composition.simps def_presv_fin_prof
        single_elim_imp_red_def_set snd_conv
  by metis

lemma seq_comp_def_set_sound:
  assumes
    "electoral_module m" and
    "electoral_module n" and
    "finite_profile A p"
  shows "defer (m \<triangleright> n) A p \<subseteq> defer m A p"
proof -
  have "\<forall>A p. finite_profile A p \<longrightarrow> well_formed A (n A p)"
    using assms(2) electoral_module_def
    by auto
  hence
    "finite_profile (defer m A p) (limit_profile (defer m A p) p) \<longrightarrow>
        well_formed (defer m A p)
          (n (defer m A p) (limit_profile (defer m A p) p))"
    by simp
  hence
    "well_formed (defer m A p) (n (defer m A p)
      (limit_profile (defer m A p) p))"
    using assms(1) assms(3) def_presv_fin_prof
    by metis
  thus ?thesis
    using assms seq_comp_def_set_bounded
    by blast
qed

lemma seq_comp_def_set_trans:
  assumes
    "a \<in> (defer (m \<triangleright> n) A p)" and
    "electoral_module m \<and> electoral_module n" and
    "finite_profile A p"
  shows
    "a \<in> defer n (defer m A p)
      (limit_profile (defer m A p) p) \<and>
      a \<in> defer m A p"
  using seq_comp_def_set_bounded assms(1) assms(2)
        assms(3) in_mono seq_comp_defers_def_set
  by (metis (no_types, hide_lams))
end
