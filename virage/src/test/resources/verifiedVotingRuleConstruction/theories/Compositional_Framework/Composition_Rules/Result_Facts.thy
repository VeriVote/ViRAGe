theory Result_Facts
  imports "../Properties/Result_Properties"
          "../Components/Basic_Modules/Elect_Module"
          "../Components/Basic_Modules/Plurality_Module"
          "../Components/Basic_Modules/Defer_Module"
          "../Components/Basic_Modules/Drop_Module"
          "../Components/Basic_Modules/Pass_Module"
          "../Components/Compositional_Structures/Revision_Composition"
          "../Components/Composites/Composite_Elimination_Modules"

begin

theorem elect_mod_electing[simp]: "electing elect_module"
  unfolding electing_def
  by simp

lemma plurality_electing2: "\<forall>A p.
                              (A \<noteq> {} \<and> finite_profile A p) \<longrightarrow>
                                elect plurality A p \<noteq> {}"
proof (intro allI impI conjI)
  fix
    A :: "'a set" and
    p :: "'a Profile"
  assume
    assm0: "A \<noteq> {} \<and> finite_profile A p"
  show
    "elect plurality A p \<noteq> {}"
  proof
    obtain max where
      max: "max = Max(win_count p ` A)"
      by simp
    then obtain a where
      a: "win_count p a = max \<and> a \<in> A"
      using Max_in assm0 empty_is_image
            finite_imageI imageE
      by (metis (no_types, lifting))
    hence
      "\<forall>x \<in> A. win_count p x \<le> win_count p a"
      by (simp add: max assm0)
    moreover have
      "a \<in> A"
      using a
      by simp
    ultimately have
      "a \<in> {a \<in> A. \<forall>x \<in> A. win_count p x \<le> win_count p a}"
      by blast
    hence a_elem:
      "a \<in> elect plurality A p"
      by simp
    assume
      assm1: "elect plurality A p = {}"
    thus "False"
      using a_elem assm1 all_not_in_conv
      by metis
  qed
qed

(*The plurality module is electing.*)
theorem plurality_electing[simp]: "electing plurality"
proof -
  have "electoral_module plurality \<and>
      (\<forall>A p. (A \<noteq> {} \<and> finite_profile A p) \<longrightarrow> elect plurality A p \<noteq> {})"
  proof
    show "electoral_module plurality"
      by simp
  next
    show "(\<forall>A p. (A \<noteq> {} \<and> finite_profile A p) \<longrightarrow> elect plurality A p \<noteq> {})"
      using plurality_electing2
      by metis
  qed
  thus ?thesis
      by (simp add: electing_def)
  qed

theorem def_mod_non_electing: "non_electing defer_module"
  unfolding non_electing_def
  by simp


(*The drop module is non-electing.*)
theorem drop_mod_non_electing[simp]:
  assumes order: "linear_order r"
  shows "non_electing (drop_module n r)"
  by (simp add: non_electing_def order)

lemma elim_mod_non_electing:
  assumes profile: "finite_profile A p"
  shows "non_electing (elimination_module e t r )"
  by (simp add: non_electing_def)

lemma less_elim_non_electing:
  assumes profile: "finite_profile A p"
  shows "non_electing (less_eliminator e t)"
  using elim_mod_non_electing profile less_elim_sound
  by (simp add: non_electing_def)

lemma leq_elim_non_electing:
  assumes profile: "finite_profile A p"
  shows "non_electing (leq_eliminator e t)"
proof -
  have "non_electing (elimination_module e t (\<le>))"
    by (simp add: non_electing_def)
  thus ?thesis
    by (simp add: non_electing_def)
qed

lemma max_elim_non_electing:
  assumes profile: "finite_profile A p"
  shows "non_electing (max_eliminator e)"
proof -
  have "non_electing (elimination_module e t (<))"
    by (simp add: non_electing_def)
  thus ?thesis
    by (simp add: non_electing_def)
qed

lemma min_elim_non_electing:
  assumes profile: "finite_profile A p"
  shows "non_electing (min_eliminator e)"
proof -
  have "non_electing (elimination_module e t (<))"
    by (simp add: non_electing_def)
  thus ?thesis
    by (simp add: non_electing_def)
qed

lemma less_avg_elim_non_electing:
  assumes profile: "finite_profile A p"
  shows "non_electing (less_average_eliminator e)"
proof -
  have "non_electing (elimination_module e t (<))"
    by (simp add: non_electing_def)
  thus ?thesis
    by (simp add: non_electing_def)
qed

lemma leq_avg_elim_non_electing:
  assumes profile: "finite_profile A p"
  shows "non_electing (leq_average_eliminator e)"
proof -
  have "non_electing (elimination_module e t (\<le>))"
    by (simp add: non_electing_def)
  thus ?thesis
    by (simp add: non_electing_def)
qed

(*The pass module is non-electing.*)
theorem pass_mod_non_electing[simp]:
  assumes order: "linear_order r"
  shows "non_electing (pass_module n r)"
  by (simp add: non_electing_def order)

(*An electoral module received by revision is never electing.*)
theorem rev_comp_non_electing[simp]:
  assumes "electoral_module m"
  shows "non_electing (m\<down>)"
  by (simp add: assms non_electing_def)

(*The pass module is non-blocking.*)
theorem pass_mod_non_blocking[simp]:
  assumes order: "linear_order r" and
          g0_n: "custom_greater n 0"
        shows "non_blocking (pass_module n r)"
  unfolding non_blocking_def
proof (safe, simp_all)
  show "electoral_module (pass_module n r)"
    using pass_mod_sound order
    by simp
next
  fix
    A :: "'a set" and
    p :: "'a Profile" and
    x :: "'a"
  assume
    fin_A: "finite A" and
    prof_A: "profile A p" and
    card_A:
    "{a \<in> A. n <
      card (above
        {(a, b). (a, b) \<in> r \<and>
          a \<in> A \<and> b \<in> A} a)} = A" and
    x_in_A: "x \<in> A"
  have lin_ord_A:
    "linear_order_on A (limit A r)"
    using limit_presv_lin_ord order top_greatest
    by metis
  have
    "\<exists>a\<in>A. above (limit A r) a = {a} \<and>
      (\<forall>x\<in>A. above (limit A r) x = {x} \<longrightarrow> x = a)"
    using above_one fin_A lin_ord_A x_in_A
    by blast
  hence not_all:
    "{a \<in> A. card(above (limit A r) a) > n} \<noteq> A"
    using One_nat_def Suc_leI assms(2) is_singletonI
          is_singleton_altdef leD mem_Collect_eq
    by (metis (no_types, lifting) custom_greater.simps) 
  hence "reject (pass_module n r) A p \<noteq> A"
    by simp
  thus "False"
    using order card_A
    by simp
qed

theorem pass_zero_mod_def_zero[simp]:
  assumes order: "linear_order r"
  shows "defers 0 (pass_module 0 r)"
  unfolding defers_def
proof (safe)
  show "electoral_module (pass_module 0 r)"
    using pass_mod_sound order
    by simp
next
  fix
    A :: "'a set" and
    p :: "'a Profile"
  assume
    card_pos: "0 \<le> card A" and
    finite_A: "finite A" and
    prof_A: "profile A p"
  show
    "card (defer (pass_module 0 r) A p) = 0"
  proof -
    have lin_ord_on_A:
      "linear_order_on A (limit A r)"
      using order limit_presv_lin_ord
      by blast
    have f1: "connex A (limit A r)"
      using lin_ord_imp_connex lin_ord_on_A
      by simp
    obtain aa :: "('a \<Rightarrow> bool) \<Rightarrow> 'a" where
      f2:
      "\<forall>p. (Collect p = {} \<longrightarrow> (\<forall>a. \<not> p a)) \<and>
            (Collect p \<noteq> {} \<longrightarrow> p (aa p))"
      by moura
    have "\<forall>n. \<not> (n::nat) \<le> 0 \<or> n = 0"
      by blast
    hence
      "\<forall>a Aa. \<not> connex Aa (limit A r) \<or> a \<notin> Aa \<or> a \<notin> A \<or>
                  \<not> card (above (limit A r) a) \<le> 0"
      using above_connex above_presv_limit card_eq_0_iff
            equals0D finite_A order rev_finite_subset
      by (metis (no_types))
    hence "{a \<in> A. card(above (limit A r) a) \<le> 0} = {}"
      using f1
      by auto
    hence "card {a \<in> A. card(above (limit A r) a) \<le> 0} = 0"
      using card.empty
      by metis
    thus "card (defer (pass_module 0 r) A p) = 0"
      by simp
  qed
qed

(*
   For any natural number n and any linear order, the according pass module
   defers n alternatives (if there are n alternatives).
   NOTE: The induction proof is still missing. Following are the proofs for
   n=1 and n=2.
*)
theorem pass_one_mod_def_one[simp]:
  assumes order: "linear_order r"
  shows "defers 1 (pass_module 1 r)"
  unfolding defers_def
proof (safe)
  show "electoral_module (pass_module 1 r)"
    using pass_mod_sound order
    by simp
next
  fix
    A :: "'a set" and
    p :: "'a Profile"
  assume
    card_pos: "1 \<le> card A" and
    finite_A: "finite A" and
    prof_A: "profile A p"
  show
    "card (defer (pass_module 1 r) A p) = 1"
  proof -
    have "A \<noteq> {}"
      using card_pos
      by auto
    moreover have lin_ord_on_A:
      "linear_order_on A (limit A r)"
      using order limit_presv_lin_ord
      by blast
    ultimately have winner_exists:
      "\<exists>a\<in>A. above (limit A r) a = {a} \<and>
        (\<forall>x\<in>A. above (limit A r) x = {x} \<longrightarrow> x = a)"
      using finite_A
      by (simp add: above_one)
    then obtain w where w_unique_top:
      "above (limit A r) w = {w} \<and>
        (\<forall>x\<in>A. above (limit A r) x = {x} \<longrightarrow> x = w)"
      using above_one
      by auto
    hence "{a \<in> A. card(above (limit A r) a) \<le> 1} = {w}"
    proof
      assume
        w_top: "above (limit A r) w = {w}" and
        w_unique: "\<forall>x\<in>A. above (limit A r) x = {x} \<longrightarrow> x = w"
      have "card (above (limit A r) w) \<le> 1"
        using w_top
        by auto
      hence "{w} \<subseteq> {a \<in> A. card(above (limit A r) a) \<le> 1}"
        using winner_exists w_unique_top
        by blast
      moreover have
        "{a \<in> A. card(above (limit A r) a) \<le> 1} \<subseteq> {w}"
      proof
        fix
          x :: "'a"
        assume x_in_winner_set:
          "x \<in> {a \<in> A. card (above (limit A r) a) \<le> 1}"
        hence x_in_A: "x \<in> A"
          by auto
        hence connex_limit:
          "connex A (limit A r)"
          using lin_ord_imp_connex lin_ord_on_A
          by simp
        hence "let q = limit A r in x \<preceq>\<^sub>q x"
          using connex_limit above_connex
                pref_imp_in_above x_in_A
          by metis
        hence "(x,x) \<in> limit A r"
          by simp
        hence x_above_x: "x \<in> above (limit A r) x"
          by (simp add: above_def)
        have "above (limit A r) x \<subseteq> A"
          using above_presv_limit order
          by fastforce
        hence above_finite: "finite (above (limit A r) x)"
          by (simp add: finite_A finite_subset)
        have "card (above (limit A r) x) \<le> 1"
          using x_in_winner_set
          by simp
        moreover have
          "card (above (limit A r) x) \<ge> 1"
          using One_nat_def Suc_leI above_finite card_eq_0_iff
                equals0D neq0_conv x_above_x
          by metis
        ultimately have
          "card (above (limit A r) x) = 1"
          by simp
        hence "{x} = above (limit A r) x"
          using is_singletonE is_singleton_altdef singletonD x_above_x
          by metis
        hence "x = w"
          using w_unique
          by (simp add: x_in_A)
        thus "x \<in> {w}"
          by simp
      qed
      ultimately have
        "{w} = {a \<in> A. card (above (limit A r) a) \<le> 1}"
        by auto
      thus ?thesis
        by simp
    qed
    hence "defer (pass_module 1 r) A p = {w}"
      by simp
    thus "card (defer (pass_module 1 r) A p) = 1"
      by simp
  qed
qed

theorem pass_two_mod_def_two:
  assumes order: "linear_order r"
  shows "defers 2 (pass_module 2 r)"
  unfolding defers_def
proof (safe)
  show "electoral_module (pass_module 2 r)"
    using order
    by simp
next
  fix
    A :: "'a set" and
    p :: "'a Profile"
  assume
    min_2_card: "2 \<le> card A" and
    finA: "finite A" and
    profA: "profile A p"
  from min_2_card
  have not_empty_A: "A \<noteq> {}"
    by auto
  moreover have limitA_order:
    "linear_order_on A (limit A r)"
    using limit_presv_lin_ord order
    by auto
  ultimately obtain a where
    a: "above (limit A r) a = {a}"
    using above_one min_2_card finA profA
    by blast
  hence "\<forall>b \<in> A. let q = limit A r in (b \<preceq>\<^sub>q a)"
    using limitA_order pref_imp_in_above empty_iff
          insert_iff insert_subset above_presv_limit
          order connex_def lin_ord_imp_connex
    by metis
  hence a_best: "\<forall>b \<in> A. (b, a) \<in> limit A r"
    by simp
  hence a_above: "\<forall>b \<in> A. a \<in> above (limit A r) b"
    by (simp add: above_def)
  from a have "a \<in> {a \<in> A. card(above (limit A r) a) \<le> 2}"
    using CollectI Suc_leI not_empty_A a_above card_UNIV_bool
          card_eq_0_iff card_insert_disjoint empty_iff finA
          finite.emptyI insert_iff limitA_order above_one
          UNIV_bool nat.simps(3) zero_less_Suc
    by (metis (no_types, lifting))
  hence a_in_defer: "a \<in> defer (pass_module 2 r) A p"
    by simp
  have "finite (A-{a})"
    by (simp add: finA)
  moreover have A_not_only_a: "A-{a} \<noteq> {}"
    using min_2_card Diff_empty Diff_idemp Diff_insert0
          One_nat_def not_empty_A card.insert_remove
          card_eq_0_iff finite.emptyI insert_Diff
          numeral_le_one_iff semiring_norm(69) card.empty
    by metis
  moreover have limitAa_order:
    "linear_order_on (A-{a}) (limit (A-{a}) r)"
    using limit_presv_lin_ord order top_greatest
    by blast
  ultimately obtain b where b: "above (limit (A-{a}) r) b = {b}"
    using above_one
    by metis
  hence "\<forall>c \<in> A-{a}. let q = limit (A-{a}) r in (c \<preceq>\<^sub>q b)"
    using limitAa_order pref_imp_in_above empty_iff insert_iff
          insert_subset above_presv_limit order connex_def
          lin_ord_imp_connex
    by metis
  hence b_in_limit: "\<forall>c \<in> A-{a}. (c, b) \<in> limit (A-{a}) r"
    by simp
  hence b_best: "\<forall>c \<in> A-{a}. (c, b) \<in> limit A r"
    by auto
  hence c_not_above_b: "\<forall>c \<in> A-{a, b}. c \<notin> above (limit A r) b"
    using b Diff_iff Diff_insert2 subset_UNIV above_presv_limit
          insert_subset order limit_presv_above limit_presv_above2
    by metis
  moreover have above_subset: "above (limit A r) b \<subseteq> A"
    using above_presv_limit order
    by metis
  moreover have b_above_b: "b \<in> above (limit A r) b"
    using above_def b b_best above_presv_limit
          mem_Collect_eq order insert_subset
    by metis
  ultimately have above_b_eq_ab: "above (limit A r) b = {a, b}"
    using a_above
    by auto
  hence card_above_b_eq_2: "card (above (limit A r) b) = 2"
    using A_not_only_a b_in_limit
    by auto
  hence b_in_defer: "b \<in> defer (pass_module 2 r) A p"
    using b_above_b above_subset
    by auto
  from b_best have b_above:
    "\<forall>c \<in> A-{a}. b \<in> above (limit A r) c"
    using above_def mem_Collect_eq
    by metis
  have "connex A (limit A r)"
    using limitA_order lin_ord_imp_connex
    by auto
  hence "\<forall>c \<in> A. c \<in> above (limit A r) c"
    by (simp add: above_connex)
  hence "\<forall>c \<in> A-{a, b}. {a, b, c} \<subseteq> above (limit A r) c"
    using a_above b_above
    by auto
  moreover have "\<forall>c \<in> A-{a, b}. card{a, b, c} = 3"
    using DiffE One_nat_def Suc_1 above_b_eq_ab card_above_b_eq_2
          above_subset card_insert_disjoint finA finite_subset
          insert_commute numeral_3_eq_3
    by metis
  ultimately have
    "\<forall>c \<in> A-{a, b}. card (above (limit A r) c) \<ge> 3"
    using card_mono finA finite_subset above_presv_limit order
    by metis
  hence "\<forall>c \<in> A-{a, b}. card (above (limit A r) c) > 2"
    using less_le_trans numeral_less_iff order_refl semiring_norm(79)
    by metis
  hence "\<forall>c \<in> A-{a, b}. c \<notin> defer (pass_module 2 r) A p"
    by (simp add: not_le)
  moreover have "defer (pass_module 2 r) A p \<subseteq> A"
    by auto
  ultimately have "defer (pass_module 2 r) A p \<subseteq> {a, b}"
    by blast
  with a_in_defer b_in_defer have
    "defer (pass_module 2 r) A p = {a, b}"
    by fastforce
  thus "card (defer (pass_module 2 r) A p) = 2"
    using above_b_eq_ab card_above_b_eq_2
    by presburger
qed

theorem drop_zero_mod_rej_zero[simp]:
  assumes order: "linear_order r"
  shows "rejects 0 (drop_module 0 r)"
  unfolding rejects_def
proof (safe)
  show "electoral_module (drop_module 0 r)"
    using order
    by simp
next
  fix
    A :: "'a set" and
    p :: "'a Profile"
  assume
    card_pos: "0 \<le> card A" and
    finite_A: "finite A" and
    prof_A: "profile A p"
  have f1: "connex UNIV r"
    using assms lin_ord_imp_connex
    by auto
  obtain aa :: "('a \<Rightarrow> bool) \<Rightarrow> 'a" where
    f2:
    "\<forall>p. (Collect p = {} \<longrightarrow> (\<forall>a. \<not> p a)) \<and>
          (Collect p \<noteq> {} \<longrightarrow> p (aa p))"
    by moura
  have f3: "\<forall>a. (a::'a) \<notin> {}"
    using empty_iff
    by simp
  have connex:
    "connex A (limit A r)"
    using f1 limit_presv_connex subset_UNIV
    by metis
  have rej_drop_eq_def_pass:
    "reject (drop_module 0 r) = defer (pass_module 0 r)"
    by simp
  have f4:
    "\<forall>a Aa.
      \<not> connex Aa (limit A r) \<or> a \<notin> Aa \<or> a \<notin> A \<or>
        \<not> card (above (limit A r) a) \<le> 0"
    using above_connex above_presv_limit bot_nat_0.extremum_uniqueI
          card_0_eq emptyE finite_A order rev_finite_subset
    by (metis (lifting))
  have "{a \<in> A. card(above (limit A r) a) \<le> 0} = {}"
    using connex f4
    by auto
  hence "card {a \<in> A. card(above (limit A r) a) \<le> 0} = 0"
    using card.empty
    by (metis (full_types))
  thus "card (reject (drop_module 0 r) A p) = 0"
    by simp
qed

(*
  The drop module rejects n alternatives (if there are n alternatives).
  NOTE: The induction proof is still missing. Following is the proof for n=2.
*)
theorem drop_two_mod_rej_two[simp]:
  assumes order: "linear_order r"
  shows "rejects 2 (drop_module 2 r)"
proof -
  have rej_drop_eq_def_pass:
    "reject (drop_module 2 r) = defer (pass_module 2 r)"
    by simp
  thus ?thesis
  proof -
    obtain
      AA :: "('a Electoral_Module) \<Rightarrow> nat \<Rightarrow> 'a set" and
      rrs :: "('a Electoral_Module) \<Rightarrow> nat \<Rightarrow> 'a Profile" where
      "\<forall>x0 x1. (\<exists>v2 v3. (x1 \<le> card v2 \<and> finite_profile v2 v3) \<and>
          card (reject x0 v2 v3) \<noteq> x1) =
              ((x1 \<le> card (AA x0 x1) \<and>
                finite_profile (AA x0 x1) (rrs x0 x1)) \<and>
                card (reject x0 (AA x0 x1) (rrs x0 x1)) \<noteq> x1)"
      by moura
    hence
      "\<forall>n f. (\<not> rejects n f \<or> electoral_module f \<and>
          (\<forall>A rs. (\<not> n \<le> card A \<or> infinite A \<or> \<not> profile A rs) \<or>
              card (reject f A rs) = n)) \<and>
          (rejects n f \<or> \<not> electoral_module f \<or> (n \<le> card (AA f n) \<and>
              finite_profile (AA f n) (rrs f n)) \<and>
              card (reject f (AA f n) (rrs f n)) \<noteq> n)"
      using rejects_def
      by force
    hence f1:
      "\<forall>n f. (\<not> rejects n f \<or> electoral_module f \<and>
        (\<forall>A rs. \<not> n \<le> card A \<or> infinite A \<or> \<not> profile A rs \<or>
            card (reject f A rs) = n)) \<and>
        (rejects n f \<or> \<not> electoral_module f \<or> n \<le> card (AA f n) \<and>
            finite (AA f n) \<and> profile (AA f n) (rrs f n) \<and>
            card (reject f (AA f n) (rrs f n)) \<noteq> n)"
      by presburger
    have
      "\<not> 2 \<le> card (AA (drop_module 2 r) 2) \<or>
          infinite (AA (drop_module 2 r) 2) \<or>
          \<not> profile (AA (drop_module 2 r) 2) (rrs (drop_module 2 r) 2) \<or>
          card (reject (drop_module 2 r) (AA (drop_module 2 r) 2)
              (rrs (drop_module 2 r) 2)) = 2"
      using rej_drop_eq_def_pass defers_def order
            pass_two_mod_def_two
      by (metis (no_types))
    thus ?thesis
      using f1 drop_mod_sound order
      by blast
  qed
qed

end