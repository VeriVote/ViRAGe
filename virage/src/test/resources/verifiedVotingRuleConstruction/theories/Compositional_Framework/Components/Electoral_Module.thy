(*  File:       Electoral_Module.thy
    Copyright   2021  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Jonas Kraemer, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Karsten Diekhoff, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Michael Kirsten, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Stephan Bohr, Karlsruhe Institute of Technology (KIT)"\<close>

chapter \<open>Component Types\<close>

section \<open>Electoral Module\<close>

theory Electoral_Module
  imports "../../Social_Choice_Types/Preference_Relation"
          "../../Social_Choice_Types/Profile"
          "../../Social_Choice_Types/Result"

begin

text
\<open>Electoral modules are the principal component type of the composable modules
voting framework, as they are a generalization of voting rules in the sense of
social choice functions.
These are only the types used for electoral modules. Further restrictions are
encompassed by the electoral-module predicate.

An electoral module does not need to make final decisions for all alternatives,
but can instead defer the decision for some or all of them to other modules.
Hence, electoral modules partition the received (possibly empty) set of
alternatives into elected, rejected and deferred alternatives. In particular,
any of those sets, e.g., the set of winning (elected) alternatives, may also
be left empty, as long as they collectively still hold all the received
alternatives. Just like a voting rule, an electoral module also receives a
profile which holds the voters’ preferences, which, unlike a voting rule,
consider only the (sub-)set of alternatives that the module receives.\<close>

subsection \<open>Definition\<close>

(*An electoral module maps a set of alternatives and a profile to a result.*)
type_synonym 'a Electoral_Module = "'a set \<Rightarrow> 'a Profile \<Rightarrow> 'a Result"

subsection \<open>Auxiliary Definitions\<close>

(*
   Electoral modules partition a given set of alternatives A into a set of
   elected alternatives e, a set of rejected alternatives r, and a set of
   deferred alternatives d, using a profile.
   e, r, and d partition A.
   Electoral modules can be used as voting rules. They can also be composed
   in multiple structures to create more complex electoral modules.
*)
definition electoral_module :: " 'a Electoral_Module \<Rightarrow> bool" where
  "electoral_module m \<equiv> \<forall>A p. finite_profile A p \<longrightarrow> well_formed A (m A p)"

lemma electoral_modI:
  "((\<And>A p. \<lbrakk> finite_profile A p \<rbrakk> \<Longrightarrow> well_formed A (m A p)) \<Longrightarrow>
       electoral_module m)"
  unfolding electoral_module_def
  by auto

(*
   The next three functions take an electoral module and turn it into a
   function only outputting the elect, reject, or defer set respectively.
*)
abbreviation elect ::
  "'a Electoral_Module \<Rightarrow> 'a set \<Rightarrow> 'a Profile \<Rightarrow> 'a set" where
  "elect m A p \<equiv> elect_r (m A p)"

abbreviation reject ::
  "'a Electoral_Module \<Rightarrow> 'a set \<Rightarrow> 'a Profile \<Rightarrow> 'a set" where
  "reject m A p \<equiv> reject_r (m A p)"

abbreviation "defer" ::
  "'a Electoral_Module \<Rightarrow> 'a set \<Rightarrow> 'a Profile \<Rightarrow> 'a set" where
  "defer m A p \<equiv> defer_r (m A p)"

(*
(*
   An Electoral module m is rejecting iff at least one alternative gets
   rejected when possible
*)
definition rejecting :: "'a Electoral_Module \<Rightarrow> bool" where
  "
  "rejecting m \<equiv> \<forall>A . card A > 1 \<longrightarrow> (\<exists>n . (n > 0 \<and> rejects n m))"

(*WRONG definition, choose `n > card A` and already it is always true.*)
(*An electoral module m is eliminating iff the following holds*)
(*
   If there is at least one alternative that can be rejected,
   at least one alternative gets rejected.
*)
definition eliminating :: "'a Electoral_Module \<Rightarrow> bool" where
  "eliminating m \<equiv>  \<exists> n . (n > 0 \<and> eliminates n m)"
*)


subsection \<open>Equivalence Definitions\<close>

definition prof_contains_result :: "'a Electoral_Module \<Rightarrow> 'a set \<Rightarrow> 'a Profile \<Rightarrow>
                                       'a Profile \<Rightarrow> 'a \<Rightarrow> bool" where
  "prof_contains_result m A p q a \<equiv>
    electoral_module m \<and> finite_profile A p \<and> finite_profile A q \<and> a \<in> A \<and>
    (a \<in> elect m A p \<longrightarrow> a \<in> elect m A q) \<and>
    (a \<in> reject m A p \<longrightarrow> a \<in> reject m A q) \<and>
    (a \<in> defer m A p \<longrightarrow> a \<in> defer m A q)"

definition prof_leq_result :: "'a Electoral_Module \<Rightarrow> 'a set \<Rightarrow> 'a Profile \<Rightarrow>
                                  'a Profile \<Rightarrow> 'a \<Rightarrow> bool" where
  "prof_leq_result m A p q a \<equiv>
    electoral_module m \<and> finite_profile A p \<and> finite_profile A q \<and> a \<in> A \<and>
    (a \<in> reject m A p \<longrightarrow> a \<in> reject m A q) \<and>
    (a \<in> defer m A p \<longrightarrow> a \<notin> elect m A q)"

definition prof_geq_result :: "'a Electoral_Module \<Rightarrow> 'a set \<Rightarrow> 'a Profile \<Rightarrow>
                                  'a Profile \<Rightarrow> 'a \<Rightarrow> bool" where
  "prof_geq_result m A p q a \<equiv>
    electoral_module m \<and> finite_profile A p \<and> finite_profile A q \<and> a \<in> A \<and>
    (a \<in> elect m A p \<longrightarrow> a \<in> elect m A q) \<and>
    (a \<in> defer m A p \<longrightarrow> a \<notin> reject m A q)"

definition mod_contains_result :: "'a Electoral_Module \<Rightarrow> 'a Electoral_Module \<Rightarrow>
                                      'a set \<Rightarrow> 'a Profile \<Rightarrow> 'a \<Rightarrow> bool" where
  "mod_contains_result m n A p a \<equiv>
    electoral_module m \<and> electoral_module n \<and> finite_profile A p \<and> a \<in> A \<and>
    (a \<in> elect m A p \<longrightarrow> a \<in> elect n A p) \<and>
    (a \<in> reject m A p \<longrightarrow> a \<in> reject n A p) \<and>
    (a \<in> defer m A p \<longrightarrow> a \<in> defer n A p)"

subsection \<open>Auxiliary Lemmata\<close>

lemma combine_ele_rej_def:
  assumes
    ele: "elect m A p = e" and
    rej: "reject m A p = r" and
    def: "defer m A p = d"
  shows "m A p = (e, r, d)"
  using def ele rej
  by auto

lemma par_comp_result_sound:
  assumes
    mod_m: "electoral_module m" and
    f_prof: "finite_profile A p"
  shows "well_formed A (m A p)"
  using electoral_module_def mod_m f_prof
  by auto

lemma result_presv_alts:
  assumes
    e_mod: "electoral_module m" and
    f_prof: "finite_profile A p"
  shows "(elect m A p) \<union> (reject m A p) \<union> (defer m A p) = A"
proof (safe)
  fix
    x :: "'a"
  assume
    asm: "x \<in> elect m A p"
  have partit:
    "\<forall>A p.
      \<not> set_equals_partition (A::'a set) p \<or>
        (\<exists>B C D E. A = B \<and> p = (C, D, E) \<and> C \<union> D \<union> E = B)"
    by simp
  from e_mod f_prof have set_partit:
    "set_equals_partition A (m A p)"
    using electoral_module_def
    by auto
  thus "x \<in> A"
    using UnI1 asm fstI set_partit partit
    by (metis (no_types))
next
  fix
    x :: "'a"
  assume
    asm: "x \<in> reject m A p"
  have partit:
    "\<forall>A p.
      \<not> set_equals_partition (A::'a set) p \<or>
        (\<exists>B C D E. A = B \<and> p = (C, D, E) \<and> C \<union> D \<union> E = B)"
    by simp
  from e_mod f_prof have set_partit:
    "set_equals_partition A (m A p)"
    using electoral_module_def
    by auto
  thus "x \<in> A"
    using UnI1 asm fstI set_partit partit
          sndI subsetD sup_ge2
    by metis
next
  fix
    x :: "'a"
  assume
    asm: "x \<in> defer m A p"
  have partit:
    "\<forall>A p.
      \<not> set_equals_partition (A::'a set) p \<or>
        (\<exists>B C D E. A = B \<and> p = (C, D, E) \<and> C \<union> D \<union> E = B)"
    by simp
  from e_mod f_prof have set_partit:
    "set_equals_partition A (m A p)"
    using electoral_module_def
    by auto
  thus "x \<in> A"
    using asm set_partit partit sndI subsetD sup_ge2
    by metis
next
  fix
    x :: "'a"
  assume
    asm1: "x \<in> A" and
    asm2: "x \<notin> defer m A p" and
    asm3: "x \<notin> reject m A p"
  have partit:
    "\<forall>A p.
      \<not> set_equals_partition (A::'a set) p \<or>
        (\<exists>B C D E. A = B \<and> p = (C, D, E) \<and> C \<union> D \<union> E = B)"
    by simp
  from e_mod f_prof have set_partit:
    "set_equals_partition A (m A p)"
    using electoral_module_def
    by auto
  show "x \<in> elect m A p"
    using asm1 asm2 asm3 fst_conv partit
          set_partit snd_conv Un_iff
    by metis
qed

lemma result_disj:
  assumes
    module: "electoral_module m" and
    profile: "finite_profile A p"
  shows
    "(elect m A p) \<inter> (reject m A p) = {} \<and>
        (elect m A p) \<inter> (defer m A p) = {} \<and>
        (reject m A p) \<inter> (defer m A p) = {}"
proof (safe, simp_all)
  fix
    x :: "'a"
  assume
    asm1: "x \<in> elect m A p" and
    asm2: "x \<in> reject m A p"
  have partit:
    "\<forall>A p.
      \<not> set_equals_partition (A::'a set) p \<or>
        (\<exists>B C D E. A = B \<and> p = (C, D, E) \<and> C \<union> D \<union> E = B)"
    by simp
  from module profile have set_partit:
    "set_equals_partition A (m A p)"
    using electoral_module_def
    by auto
  from profile have prof_p:
    "finite A \<and> profile A p"
    by simp
  from module prof_p have wf_A_m:
    "well_formed A (m A p)"
    using electoral_module_def
    by metis
  show "False"
    using prod.exhaust_sel DiffE UnCI asm1 asm2
          module profile result_imp_rej wf_A_m
          prof_p set_partit partit
    by (metis (no_types))
next
  fix
    x :: "'a"
  assume
    asm1: "x \<in> elect m A p" and
    asm2: "x \<in> defer m A p"
  have partit:
    "\<forall>A p.
      \<not> set_equals_partition (A::'a set) p \<or>
        (\<exists>B C D E. A = B \<and> p = (C, D, E) \<and> C \<union> D \<union> E = B)"
    by simp
  have disj:
    "\<forall>p. \<not> disjoint3 p \<or>
      (\<exists>B C D. p = (B::'a set, C, D) \<and>
        B \<inter> C = {} \<and> B \<inter> D = {} \<and> C \<inter> D = {})"
    by simp
  from profile have prof_p:
    "finite A \<and> profile A p"
    by simp
  from module prof_p have wf_A_m:
    "well_formed A (m A p)"
    using electoral_module_def
    by metis
  hence wf_A_m_0:
    "disjoint3 (m A p) \<and> set_equals_partition A (m A p)"
    by simp
  hence disj3:
    "disjoint3 (m A p)"
    by simp
  have set_partit:
    "set_equals_partition A (m A p)"
    using wf_A_m_0
    by simp
  from disj3 obtain
    AA :: "'a Result \<Rightarrow> 'a set" and
    AAa :: "'a Result \<Rightarrow> 'a set" and
    AAb :: "'a Result \<Rightarrow> 'a set"
    where
    "m A p =
      (AA (m A p), AAa (m A p), AAb (m A p)) \<and>
        AA (m A p) \<inter> AAa (m A p) = {} \<and>
        AA (m A p) \<inter> AAb (m A p) = {} \<and>
        AAa (m A p) \<inter> AAb (m A p) = {}"
    using asm1 asm2 disj
    by metis
  hence "((elect m A p) \<inter> (reject m A p) = {}) \<and>
          ((elect m A p) \<inter> (defer m A p) = {}) \<and>
          ((reject m A p) \<inter> (defer m A p) = {})"
    using disj3 eq_snd_iff fstI
    by metis
  thus "False"
    using asm1 asm2 module profile wf_A_m prof_p
          set_partit partit disjoint_iff_not_equal
    by (metis (no_types))
next
  fix
    x :: "'a"
  assume
    asm1: "x \<in> reject m A p" and
    asm2: "x \<in> defer m A p"
  have partit:
    "\<forall>A p.
      \<not> set_equals_partition (A::'a set) p \<or>
        (\<exists>B C D E. A = B \<and> p = (C, D, E) \<and> C \<union> D \<union> E = B)"
    by simp
  from module profile have set_partit:
    "set_equals_partition A (m A p)"
    using electoral_module_def
    by auto
  from profile have prof_p:
    "finite A \<and> profile A p"
    by simp
  from module prof_p have wf_A_m:
    "well_formed A (m A p)"
    using electoral_module_def
    by metis
  show "False"
    using prod.exhaust_sel DiffE UnCI asm1 asm2
          module profile result_imp_rej wf_A_m
          prof_p set_partit partit
    by (metis (no_types))
qed

lemma elect_in_alts:
  assumes
    e_mod: "electoral_module m" and
    f_prof: "finite_profile A p"
  shows "elect m A p \<subseteq> A"
  using le_supI1 e_mod f_prof result_presv_alts sup_ge1
  by metis

lemma reject_in_alts:
  assumes
    e_mod: "electoral_module m" and
    f_prof: "finite_profile A p"
  shows "reject m A p \<subseteq> A"
  using le_supI1 e_mod f_prof result_presv_alts sup_ge2
  by fastforce

lemma defer_in_alts:
  assumes
    e_mod: "electoral_module m" and
    f_prof: "finite_profile A p"
  shows "defer m A p \<subseteq> A"
  using e_mod f_prof result_presv_alts
  by auto

lemma def_presv_fin_prof:
  assumes module:  "electoral_module m" and
          f_prof: "finite_profile A p"
  shows
    "let new_A = defer m A p in
        finite_profile new_A (limit_profile new_A p)"
  using defer_in_alts infinite_super
        limit_profile_sound module f_prof
  by metis

(*
   An electoral module can never reject, defer or elect more than
   |A| alternatives.
*)
lemma upper_card_bounds_for_result:
  assumes
    e_mod: "electoral_module m" and
    f_prof: "finite_profile A p"
  shows
    "card (elect m A p) \<le> card A \<and>
      card (reject m A p) \<le> card A \<and>
      card (defer m A p) \<le> card A "
  by (simp add: card_mono defer_in_alts elect_in_alts
                e_mod f_prof reject_in_alts)

lemma reject_not_elec_or_def:
  assumes
    e_mod: "electoral_module m" and
    f_prof: "finite_profile A p"
  shows "reject m A p = A - (elect m A p) - (defer m A p)"
proof -
  from e_mod f_prof have 0: "well_formed A (m A p)"
    by (simp add: electoral_module_def)
  with e_mod f_prof
    have "(elect m A p) \<union> (reject m A p) \<union> (defer m A p) = A"
      using result_presv_alts
      by simp
    moreover from 0 have
      "(elect m A p) \<inter> (reject m A p) = {} \<and>
          (reject m A p) \<inter> (defer m A p) = {}"
    using e_mod f_prof result_disj
    by blast
  ultimately show ?thesis
    by blast
qed

lemma elec_and_def_not_rej:
  assumes
    e_mod: "electoral_module m" and
    f_prof: "finite_profile A p"
  shows "elect m A p \<union> defer m A p = A - (reject m A p)"
proof -
  from e_mod f_prof have 0: "well_formed A (m A p)"
    by (simp add: electoral_module_def)
  hence
    "disjoint3 (m A p) \<and> set_equals_partition A (m A p)"
    by simp
  with e_mod f_prof
  have "(elect m A p) \<union> (reject m A p) \<union> (defer m A p) = A"
    using e_mod f_prof result_presv_alts
    by blast
  moreover from 0 have
    "(elect m A p) \<inter> (reject m A p) = {} \<and>
        (reject m A p) \<inter> (defer m A p) = {}"
    using e_mod f_prof result_disj
    by blast
  ultimately show ?thesis
    by blast
qed

lemma defer_not_elec_or_rej:
  assumes
    e_mod: "electoral_module m" and
    f_prof: "finite_profile A p"
  shows "defer m A p = A - (elect m A p) - (reject m A p)"
proof -
  from e_mod f_prof have 0: "well_formed A (m A p)"
    by (simp add: electoral_module_def)
  hence "(elect m A p) \<union> (reject m A p) \<union> (defer m A p) = A"
    using e_mod f_prof result_presv_alts
    by auto
  moreover from 0 have
    "(elect m A p) \<inter> (defer m A p) = {} \<and>
        (reject m A p) \<inter> (defer m A p) = {}"
      using e_mod f_prof result_disj
      by blast
  ultimately show ?thesis
    by blast
qed

lemma electoral_mod_defer_elem:
  assumes
    e_mod: "electoral_module m" and
    f_prof: "finite_profile A p" and
    alternative: "x \<in> A" and
    not_elected: "x \<notin> elect m A p" and
    not_rejected: "x \<notin> reject m A p"
  shows "x \<in> defer m A p"
  using DiffI e_mod f_prof alternative
        not_elected not_rejected
        reject_not_elec_or_def
  by metis

lemma mod_contains_result_comm:
  assumes "mod_contains_result m n A p a"
  shows "mod_contains_result n m A p a"
  using IntI assms electoral_mod_defer_elem empty_iff
        mod_contains_result_def result_disj
  by (smt (verit, ccfv_threshold))

lemma not_rej_imp_elec_or_def:
  assumes
    e_mod: "electoral_module m" and
    f_prof: "finite_profile A p" and
    alternative: "x \<in> A" and
    not_rejected: "x \<notin> reject m A p"
  shows "x \<in> elect m A p \<or> x \<in> defer m A p"
  using alternative electoral_mod_defer_elem
        e_mod not_rejected f_prof
  by metis

lemma eq_alts_in_profs_imp_eq_results:
  assumes
    eq: "\<forall>a \<in> A. prof_contains_result m A p q a" and
    (*for empty A*)
    input: "electoral_module m \<and> finite_profile A p \<and> finite_profile A q"
  shows "m A p = m A q"
proof -
  have "\<forall>a \<in> elect m A p. a \<in> elect m A q"
    using elect_in_alts eq prof_contains_result_def input in_mono
    by metis
  moreover have "\<forall>a \<in> elect m A q. a \<in> elect m A p"
    using contra_subsetD disjoint_iff_not_equal elect_in_alts
          electoral_mod_defer_elem eq prof_contains_result_def input
          result_disj
    by (smt (verit, best))
  moreover have "\<forall>a \<in> reject m A p. a \<in> reject m A q"
    using reject_in_alts eq prof_contains_result_def input in_mono
    by fastforce
  moreover have "\<forall>a \<in> reject m A q. a \<in> reject m A p"
    using contra_subsetD disjoint_iff_not_equal reject_in_alts
          electoral_mod_defer_elem eq prof_contains_result_def
          input result_disj
    by (smt (verit, ccfv_SIG))
  moreover have "\<forall>a \<in> defer m A p. a \<in> defer m A q"
    using defer_in_alts eq prof_contains_result_def input in_mono
    by fastforce
  moreover have "\<forall>a \<in> defer m A q. a \<in> defer m A p"
    using contra_subsetD disjoint_iff_not_equal defer_in_alts
          electoral_mod_defer_elem eq prof_contains_result_def
          input result_disj
    by (smt (verit, best))
  ultimately show ?thesis
    using prod.collapse subsetI subset_antisym
    by metis
qed

lemma eq_def_and_elect_imp_eq:
  assumes
    "electoral_module m" and
    "electoral_module n" and
    "finite_profile A p" and
    "finite_profile A q" and
    "elect m A p = elect n A q" and
    "defer m A p = defer n A q"
  shows "m A p = n A q"
proof -
  have disj_m:
    "disjoint3 (m A p)"
    using assms(1) assms(3) electoral_module_def
    by auto
  have disj_n:
    "disjoint3 (n A q)"
    using assms(2) assms(4) electoral_module_def
    by auto
  have set_partit_m:
    "set_equals_partition A ((elect m A p), (reject m A p), (defer m A p))"
    using assms(1) assms(3) electoral_module_def
    by auto
  moreover have
    "disjoint3 ((elect m A p),(reject m A p),(defer m A p))"
    using disj_m prod.collapse
    by metis
  have set_partit_n:
    "set_equals_partition A ((elect n A q), (reject n A q), (defer n A q))"
    using assms(2) assms(4) electoral_module_def
    by auto
  moreover have
    "disjoint3 ((elect n A q),(reject n A q),(defer n A q))"
    using disj_n prod.collapse
    by metis
  have reject_p:
    "reject m A p = A - ((elect m A p) \<union> (defer m A p))"
    using assms(1) assms(3) combine_ele_rej_def
          electoral_module_def result_imp_rej
    by metis
  have reject_q:
    "reject n A q = A - ((elect n A q) \<union> (defer n A q))"
    using assms(2) assms(4) combine_ele_rej_def
          electoral_module_def result_imp_rej
    by metis
  from reject_p reject_q show ?thesis
    by (simp add: assms(5) assms(6) prod_eqI)
qed

end
