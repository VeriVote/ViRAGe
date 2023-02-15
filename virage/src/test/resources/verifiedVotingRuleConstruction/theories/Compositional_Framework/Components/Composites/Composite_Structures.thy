theory Composite_Structures
  imports "../Electoral_Module"
          "../Basic_Modules/Elect_Module"
          "../Basic_Modules/Maximum_Aggregator"
          "../Basic_Modules/Defer_Equal_Condition"
          "../Compositional_Structures/Sequential_Composition"
          "../Compositional_Structures/Parallel_Composition"
          "../Compositional_Structures/Loop_Composition"
          "../../Properties/Aggregator_Properties"
          "../../Properties/Disjoint_Compatibility"
          "../../Composition_Rules/Aggregator_Facts"

begin

section \<open>Elect Composition\<close>

text
\<open>The elect composition sequences an electoral module and the elect
module. It finalizes the module's decision as it simply elects all their
non-rejected alternatives. Thereby, any such elect-composed module induces
a proper voting rule in the social choice sense, as all alternatives are either
rejected or elected.\<close>

subsection \<open>Definition\<close>

fun elector :: "'a Electoral_Module \<Rightarrow> 'a Electoral_Module" where
  "elector m = (m \<triangleright> elect_module)"

subsection \<open>Soundness\<close>

theorem elector_sound[simp]:
  assumes module_m: "electoral_module m"
  shows "electoral_module (elector m)"
  by (simp add: module_m)

section \<open>Defer One Loop Composition\<close>

text
\<open>This is a family of loop compositions. It uses the same module in sequence
until either no new decisions are made or only one alternative is remaining
in the defer-set. The second family herein uses the above family and
subsequently elects the remaining alternative.\<close>

subsection \<open>Definition\<close>

fun iter :: "'a Electoral_Module \<Rightarrow> 'a Electoral_Module" where
  "iter m =
    (let t = defer_equal_condition 1 in
      (m \<circlearrowleft>\<^sub>t))"

abbreviation defer_one_loop ::
  "'a Electoral_Module \<Rightarrow> 'a Electoral_Module"
    ("_\<circlearrowleft>\<^sub>\<exists>\<^sub>!\<^sub>d" 50) where
  "m \<circlearrowleft>\<^sub>\<exists>\<^sub>!\<^sub>d \<equiv> iter m"

fun iterelect :: "'a Electoral_Module \<Rightarrow> 'a Electoral_Module" where
  "iterelect m = elector (m \<circlearrowleft>\<^sub>\<exists>\<^sub>!\<^sub>d)"

section \<open>Maximum Parallel Composition\<close>

text
\<open>This is a family of parallel compositions. It composes a new electoral module
from two electoral modules combined with the maximum aggregator. Therein, the
two modules each make a decision and then a partition is returned where every
alternative receives the maximum result of the two input partitions. This means
that, if any alternative is elected by at least one of the modules, then it
gets elected, if any non-elected alternative is deferred by at least one of the
modules, then it gets deferred, only alternatives rejected by both modules get
rejected.\<close>

subsection \<open>Definition\<close>

fun maximum_parallel_composition :: "'a Electoral_Module \<Rightarrow>
        'a Electoral_Module \<Rightarrow> 'a Electoral_Module" where
  "maximum_parallel_composition m n =
    (let a = max_aggregator in (m \<parallel>\<^sub>a n))"

abbreviation max_parallel :: "'a Electoral_Module \<Rightarrow> 'a Electoral_Module \<Rightarrow>
        'a Electoral_Module" (infix "\<parallel>\<^sub>\<up>" 50) where
  "m \<parallel>\<^sub>\<up> n == maximum_parallel_composition m n"

subsection \<open>Soundness\<close>

theorem max_par_comp_sound:
  assumes
    mod_m: "electoral_module m" and
    mod_n: "electoral_module n"
  shows "electoral_module (m \<parallel>\<^sub>\<up> n)"
  using mod_m mod_n
  by simp

subsection \<open>Lemmata\<close>

lemma max_agg_eq_result:
  assumes
    module_m: "electoral_module m" and
    module_n: "electoral_module n" and
    f_prof: "finite_profile A p" and
    in_A: "x \<in> A"
  shows
    "mod_contains_result (m \<parallel>\<^sub>\<up> n) m A p x \<or>
      mod_contains_result (m \<parallel>\<^sub>\<up> n) n A p x"
proof cases
  assume a1: "x \<in> elect (m \<parallel>\<^sub>\<up> n) A p"
  hence
    "let (e1, r1, d1) = m A p;
        (e2, r2, d2) = n A p in
      x \<in> e1 \<union> e2"
    by auto
  hence "x \<in> (elect m A p) \<union> (elect n A p)"
    by auto
  thus ?thesis
    using IntI Un_iff a1 empty_iff mod_contains_result_def
          in_A max_agg_sound module_m module_n par_comp_sound
          f_prof result_disj maximum_parallel_composition.simps
    by (smt (verit, ccfv_threshold))
next
  assume not_a1: "x \<notin> elect (m \<parallel>\<^sub>\<up> n) A p"
  thus ?thesis
  proof cases
    assume a2: "x \<in> defer (m \<parallel>\<^sub>\<up> n) A p"
    thus ?thesis
      using CollectD DiffD1 DiffD2 max_aggregator.simps Un_iff
            case_prod_conv defer_not_elec_or_rej max_agg_sound
            mod_contains_result_def module_m module_n par_comp_sound
            parallel_composition.simps prod.collapse f_prof sndI
            Int_iff electoral_mod_defer_elem electoral_module_def
            max_agg_rej_set prod.sel(1) maximum_parallel_composition.simps
      by (smt (verit, del_insts))
  next
    assume not_a2: "x \<notin> defer (m \<parallel>\<^sub>\<up> n) A p"
    with not_a1 have a3:
      "x \<in> reject (m \<parallel>\<^sub>\<up> n) A p"
      using electoral_mod_defer_elem in_A max_agg_sound module_m module_n
            par_comp_sound f_prof maximum_parallel_composition.simps
      by metis
    hence
      "let (e1, r1, d1) = m A p;
          (e2, r2, d2) = n A p in
        x \<in> fst (snd (max_aggregator A (e1, r1, d1) (e2, r2, d2)))"
      using case_prod_unfold parallel_composition.simps
            surjective_pairing maximum_parallel_composition.simps
      by (smt (verit, ccfv_threshold))
    hence
      "let (e1, r1, d1) = m A p;
          (e2, r2, d2) = n A p in
        x \<in> A - (e1 \<union> e2 \<union> d1 \<union> d2)"
      by simp
    thus ?thesis
      using Un_iff combine_ele_rej_def agg_conservative_def
            contra_subsetD disjoint_iff_not_equal in_A
            electoral_module_def mod_contains_result_def
            max_agg_consv module_m module_n par_comp_sound
            parallel_composition.simps f_prof result_disj
            max_agg_rej_set not_a1 not_a2 Int_iff
            maximum_parallel_composition.simps
      by (smt (verit, del_insts))
  qed
qed

lemma max_agg_rej_iff_both_reject:
  assumes
    f_prof: "finite_profile A p" and
    module_m: "electoral_module m" and
    module_n: "electoral_module n"
  shows
    "x \<in> reject (m \<parallel>\<^sub>\<up> n) A p \<longleftrightarrow>
      (x \<in> reject m A p \<and> x \<in> reject n A p)"
proof -
  have
    "x \<in> reject (m \<parallel>\<^sub>\<up> n) A p \<longrightarrow>
      (x \<in> reject m A p \<and> x \<in> reject n A p)"
  proof
    assume a: "x \<in> reject (m \<parallel>\<^sub>\<up> n) A p"
    hence
      "let (e1, r1, d1) = m A p;
          (e2, r2, d2) = n A p in
        x \<in> fst (snd (max_aggregator A (e1, r1, d1) (e2, r2, d2)))"
      using case_prodI2 maximum_parallel_composition.simps split_def
            parallel_composition.simps prod.collapse split_beta
      by (smt (verit, ccfv_threshold))
    hence
      "let (e1, r1, d1) = m A p;
          (e2, r2, d2) = n A p in
        x \<in> A - (e1 \<union> e2 \<union> d1 \<union> d2)"
      by simp
    thus "x \<in> reject m A p \<and> x \<in> reject n A p"
      using Int_iff a electoral_module_def max_agg_rej_set module_m
            module_n parallel_composition.simps surjective_pairing
            maximum_parallel_composition.simps f_prof
      by (smt (verit, best))
  qed
  moreover have
    "(x \<in> reject m A p \<and> x \<in> reject n A p) \<longrightarrow>
        x \<in> reject (m \<parallel>\<^sub>\<up> n) A p"
  proof
    assume a: "x \<in> reject m A p \<and> x \<in> reject n A p"
    hence
      "x \<notin> elect m A p \<and> x \<notin> defer m A p \<and>
        x \<notin> elect n A p \<and> x \<notin> defer n A p"
      using IntI empty_iff module_m module_n f_prof result_disj
      by metis
    thus "x \<in> reject (m \<parallel>\<^sub>\<up> n) A p"
      using CollectD DiffD1 max_aggregator.simps Un_iff a
            electoral_mod_defer_elem prod.simps max_agg_sound
            module_m module_n f_prof old.prod.inject par_comp_sound
            prod.collapse parallel_composition.simps
            reject_not_elec_or_def maximum_parallel_composition.simps
      by (smt (verit, ccfv_threshold))
  qed
  ultimately show ?thesis
    by blast
qed

lemma max_agg_rej1:
  assumes
    f_prof: "finite_profile A p" and
    module_m: "electoral_module m" and
    module_n: "electoral_module n" and
    rejected: "x \<in> reject n A p"
  shows
    "mod_contains_result m (m \<parallel>\<^sub>\<up> n) A p x"
  using Set.set_insert contra_subsetD disjoint_insert
        mod_contains_result_comm mod_contains_result_def
        max_agg_eq_result max_agg_rej_iff_both_reject
        module_m module_n f_prof reject_in_alts rejected
        result_disj
  by (smt (verit, best))

lemma max_agg_rej2:
  assumes
    f_prof: "finite_profile A p" and
    module_m: "electoral_module m" and
    module_n: "electoral_module n" and
    rejected: "x \<in> reject n A p"
  shows
    "mod_contains_result (m \<parallel>\<^sub>\<up> n) m A p x"
  using mod_contains_result_comm max_agg_rej1
        module_m module_n f_prof rejected
  by metis

lemma max_agg_rej3:
  assumes
    f_prof:  "finite_profile A p" and
    module_m: "electoral_module m" and
    module_n: "electoral_module n" and
    rejected: "x \<in> reject m A p"
  shows
    "mod_contains_result n (m \<parallel>\<^sub>\<up> n) A p x"
  using contra_subsetD disjoint_iff_not_equal result_disj
        mod_contains_result_comm mod_contains_result_def
        max_agg_eq_result max_agg_rej_iff_both_reject
        module_m module_n f_prof reject_in_alts rejected
  by (smt (verit, ccfv_SIG))

lemma max_agg_rej4:
  assumes
    f_prof: "finite_profile A p" and
    module_m: "electoral_module m" and
    module_n: "electoral_module n" and
    rejected: "x \<in> reject m A p"
  shows
    "mod_contains_result (m \<parallel>\<^sub>\<up> n) n A p x"
  using mod_contains_result_comm max_agg_rej3
        module_m module_n f_prof rejected
  by metis

lemma max_agg_rej_intersect:
  assumes
    module_m: "electoral_module m" and
    module_n: "electoral_module n" and
    f_prof: "finite_profile A p"
  shows
    "reject (m \<parallel>\<^sub>\<up> n) A p =
      (reject m A p) \<inter> (reject n A p)"
proof -
  have
    "A = (elect m A p) \<union> (reject m A p) \<union> (defer m A p) \<and>
      A = (elect n A p) \<union> (reject n A p) \<union> (defer n A p)"
    by (simp add: module_m module_n f_prof result_presv_alts)
  hence
    "A - ((elect m A p) \<union> (defer m A p)) = (reject m A p) \<and>
      A - ((elect n A p) \<union> (defer n A p)) = (reject n A p)"
    using module_m module_n f_prof reject_not_elec_or_def
    by auto
  hence
    "A - ((elect m A p) \<union> (elect n A p) \<union> (defer m A p) \<union> (defer n A p)) =
      (reject m A p) \<inter> (reject n A p)"
    by blast
  hence
    "let (e1, r1, d1) = m A p;
        (e2, r2, d2) = n A p in
      A - (e1 \<union> e2 \<union> d1 \<union> d2) = r1 \<inter> r2"
    by fastforce
  thus ?thesis
    by auto
qed

lemma dcompat_dec_by_one_mod:
  assumes
    compatible: "disjoint_compatibility m n" and
    in_A: "x \<in> A"
  shows
    "(\<forall>p. finite_profile A p \<longrightarrow>
          mod_contains_result m (m \<parallel>\<^sub>\<up> n) A p x) \<or>
        (\<forall>p. finite_profile A p \<longrightarrow>
          mod_contains_result n (m \<parallel>\<^sub>\<up> n) A p x)"
  using DiffI compatible disjoint_compatibility_def
        in_A max_agg_rej1 max_agg_rej3
  by metis

lemma par_comp_rej_card:
  assumes
    compatible: "disjoint_compatibility x y" and
    f_prof: "finite_profile S p" and
    reject_sum: "card (reject x S p) + card (reject y S p) = card S + n"
  shows "card (reject (x \<parallel>\<^sub>\<up> y) S p) = n"
proof -
  from compatible obtain A where A:
    "A \<subseteq> S \<and>
      (\<forall>a \<in> A. indep_of_alt x S a \<and>
          (\<forall>p. finite_profile S p \<longrightarrow> a \<in> reject x S p)) \<and>
      (\<forall>a \<in> S-A. indep_of_alt y S a \<and>
          (\<forall>p. finite_profile S p \<longrightarrow> a \<in> reject y S p))"
    using disjoint_compatibility_def f_prof
    by metis
  from f_prof compatible
  have reject_representation:
    "reject (x \<parallel>\<^sub>\<up> y) S p = (reject x S p) \<inter> (reject y S p)"
    using max_agg_rej_intersect disjoint_compatibility_def
    by blast
  have "electoral_module x \<and> electoral_module y"
    using compatible disjoint_compatibility_def
    by auto
  hence subsets: "(reject x S p) \<subseteq> S \<and> (reject y S p) \<subseteq> S"
    by (simp add: f_prof reject_in_alts)
  hence "finite (reject x S p) \<and> finite (reject y S p)"
    using rev_finite_subset f_prof reject_in_alts
    by auto
  hence 0:
    "card (reject (x \<parallel>\<^sub>\<up> y) S p) =
        card S + n -
          card ((reject x S p) \<union> (reject y S p))"
    using card_Un_Int reject_representation reject_sum
    by fastforce
  have "\<forall>a \<in> S. a \<in> (reject x S p) \<or> a \<in> (reject y S p)"
    using A f_prof
    by blast
  hence 1: "card ((reject x S p) \<union> (reject y S p)) = card S"
    using subsets subset_eq sup.absorb_iff1
          sup.cobounded1 sup_left_commute
    by (smt (verit, best))
  from 0 1
  show "card (reject (x \<parallel>\<^sub>\<up> y) S p) = n"
    by simp
qed

end