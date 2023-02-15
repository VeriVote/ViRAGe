(*  File:       Plurality_Module.thy
    Copyright   2021  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Karsten Diekhoff, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Jonas Kraemer, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Michael Kirsten, Karlsruhe Institute of Technology (KIT)"\<close>

section \<open>Plurality Module\<close>

theory Plurality_Module
  imports "Component_Types/Electoral_Module"
begin

text
\<open>The plurality module implements the plurality voting rule.
The plurality rule elects all modules with the maximum amount of top
preferences among all alternatives, and rejects all the other alternatives.
It is electing and induces the classical plurality (voting) rule
from social-choice theory.\<close>

subsection \<open>Definition\<close>

fun plurality :: "'a Electoral_Module" where
  "plurality A p =
    ({a \<in> A. \<forall>x \<in> A. win_count p x \<le> win_count p a},
     {a \<in> A. \<exists>x \<in> A. win_count p x > win_count p a},
     {})"

fun plurality_code :: "'a Electoral_Module" where
  "plurality_code A p =
    ({a \<in> A. \<forall>x \<in> A. win_count_code p x \<le> win_count_code p a},
     {a \<in> A. \<exists>x \<in> A. win_count_code p x > win_count_code p a},
     {})"

subsection \<open>Soundness\<close>

theorem plurality_sound[simp]: "electoral_module plurality"
proof -
  have
    "\<forall>A p.
      let elect = {a \<in> (A::'a set). \<forall>x \<in> A. win_count p x \<le> win_count p a};
      reject = {a \<in> A. \<exists>x \<in> A. win_count p x > win_count p a} in
    elect \<inter> reject = {}"
    by auto
  hence disjoint:
    "\<forall>A p.
      let elect = {a \<in> (A::'a set). \<forall>x \<in> A. win_count p x \<le> win_count p a};
      reject = {a \<in> A. \<exists>x \<in> A. win_count p x > win_count p a} in
    disjoint3 (elect, reject, {})"
    by simp
  have
    "\<forall>A p.
      let elect = {a \<in> (A::'a set). \<forall>x \<in> A. win_count p x \<le> win_count p a};
      reject = {a \<in> A. \<exists>x \<in> A. win_count p x > win_count p a} in
    elect \<union> reject = A"
    using not_le_imp_less
    by auto
  hence unity:
    "\<forall>A p.
      let elect = {a \<in> (A::'a set). \<forall>x \<in> A. win_count p x \<le> win_count p a};
      reject = {a \<in> A. \<exists>x \<in> A. win_count p x > win_count p a} in
    set_equals_partition A (elect, reject, {})"
    by simp
  from disjoint unity show ?thesis
    by (simp add: electoral_modI)
qed

subsection \<open>Electing\<close>

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

subsection \<open>Property\<close>

lemma plurality_inv_mono2: "\<forall>A p q a.
                              (a \<in> elect plurality A p \<and> lifted A p q a) \<longrightarrow>
                                (elect plurality A q = elect plurality A p \<or>
                                    elect plurality A q = {a})"
proof (intro allI impI)
  fix
    A :: "'a set" and
    p :: "'a Profile" and
    q :: "'a Profile" and
    a :: "'a"
  assume
    asm1:
    "a \<in> elect plurality A p \<and> lifted A p q a"
  show
    "elect plurality A q = elect plurality A p \<or>
        elect plurality A q = {a}"
  proof -
    have lifted_winner:
      "\<forall>x \<in> A.
         \<forall>i::nat. i < size p \<longrightarrow>
           (above (p!i) x = {x} \<longrightarrow>
              (above (q!i) x = {x} \<or> above (q!i) a = {a}))"
      using asm1 Profile.lifted_def lifted_above_winner
      by (metis (no_types, lifting))
    hence
      "\<forall>i::nat. i < size p \<longrightarrow>
          (above (p!i) a = {a} \<longrightarrow> above (q!i) a = {a})"
      using asm1
      by auto
    hence a_win_subset:
      "{i::nat. i < size p \<and> above (p!i) a = {a}} \<subseteq>
          {i::nat. i < size p \<and> above (q!i) a = {a}}"
      by blast
    moreover have sizes:
      "size p = size q"
      using asm1 Profile.lifted_def
      by metis
    ultimately have win_count_a:
      "win_count p a \<le> win_count q a"
      by (simp add: card_mono)
    have fin_A:
      "finite A"
      using asm1 Profile.lifted_def
      by metis
    hence
      "\<forall>x \<in> A-{a}.
        \<forall>i::nat. i < size p \<longrightarrow>
          (above (q!i) a = {a} \<longrightarrow> above (q!i) x \<noteq> {x})"
      using DiffE Profile.lifted_def above_one2
            asm1 insertCI insert_absorb insert_not_empty
            profile_def sizes
      by metis
    with lifted_winner have above_QtoP:
      "\<forall>x \<in> A-{a}.
        \<forall>i::nat. i < size p \<longrightarrow>
          (above (q!i) x = {x} \<longrightarrow> above (p!i) x = {x})"
      using lifted_above_winner3 asm1
            Profile.lifted_def
      by metis
    hence
      "\<forall>x \<in> A-{a}.
        {i::nat. i < size p \<and> above (q!i) x = {x}} \<subseteq>
          {i::nat. i < size p \<and> above (p!i) x = {x}}"
      by (simp add: Collect_mono)
    hence win_count_other:
      "\<forall>x \<in> A-{a}. win_count p x \<ge> win_count q x"
      by (simp add: card_mono sizes)
    show
      "elect plurality A q = elect plurality A p \<or>
           elect plurality A q = {a}"
    proof cases
      assume "win_count p a = win_count q a"
      hence
        "card {i::nat. i < size p \<and> above (p!i) a = {a}} =
              card {i::nat. i < size p \<and> above (q!i) a = {a}}"
        by (simp add: sizes)
      moreover have
        "finite {i::nat. i < size p \<and> above (q!i) a = {a}}"
        by simp
      ultimately have
        "{i::nat. i < size p \<and> above (p!i) a = {a}} =
              {i::nat. i < size p \<and> above (q!i) a = {a}}"
        using a_win_subset
        by (simp add: card_subset_eq)
      hence above_pq:
        "\<forall>i::nat. i < size p \<longrightarrow>
            above (p!i) a = {a} \<longleftrightarrow> above (q!i) a = {a}"
        by blast
      moreover have
        "\<forall>x \<in> A-{a}.
          \<forall>i::nat. i < size p \<longrightarrow>
            (above (p!i) x = {x} \<longrightarrow>
              (above (q!i) x = {x} \<or> above (q!i) a = {a}))"
        using lifted_winner
        by auto
      moreover have
        "\<forall>x \<in> A-{a}.
          \<forall>i::nat. i < size p \<longrightarrow>
            (above (p!i) x = {x} \<longrightarrow> above (p!i) a \<noteq> {a})"
      proof (rule ccontr)
        assume
          "\<not>(\<forall>x \<in> A-{a}.
              \<forall>i::nat. i < size p \<longrightarrow>
                (above (p!i) x = {x} \<longrightarrow> above (p!i) a \<noteq> {a}))"
        hence
          "\<exists>x \<in> A-{a}.
            \<exists>i::nat.
              i < size p \<and> above (p!i) x = {x} \<and> above (p!i) a = {a}"
          by auto
        moreover from this have
          "finite A \<and> A \<noteq> {}"
          using fin_A
          by blast
        moreover from asm1 have
          "\<forall>i::nat. i < size p \<longrightarrow> linear_order_on A (p!i)"
          by (simp add: Profile.lifted_def profile_def)
        ultimately have
          "\<exists>x \<in> A-{a}. x = a"
          using above_one2
          by metis
        thus "False"
          by simp
      qed
      ultimately have above_PtoQ:
        "\<forall>x \<in> A-{a}.
          \<forall>i::nat. i < size p \<longrightarrow>
            (above (p!i) x = {x} \<longrightarrow> above (q!i) x = {x})"
        by (simp add: above_pq)
      hence
        "\<forall>x \<in> A.
          card {i::nat. i < size p \<and> above (p!i) x = {x}} =
            card {i::nat. i < size q \<and> above (q!i) x = {x}}"
        using Collect_cong DiffI above_pq above_QtoP
              insert_absorb insert_iff insert_not_empty sizes
        by (smt (verit, ccfv_threshold))
      hence "\<forall>x \<in> A. win_count p x = win_count q x"
        by simp
      hence
        "{a \<in> A. \<forall>x \<in> A. win_count p x \<le> win_count p a} =
            {a \<in> A. \<forall>x \<in> A. win_count q x \<le> win_count q a}"
        by auto
      thus ?thesis
        by simp
    next
      assume "win_count p a \<noteq> win_count q a"
      hence strict_less:
        "win_count p a < win_count q a"
        using win_count_a
        by auto
      have a_in_win_p:
        "a \<in> {a \<in> A. \<forall>x \<in> A. win_count p x \<le> win_count p a}"
        using asm1
        by auto
      hence "\<forall>x \<in> A. win_count p x \<le> win_count p a"
        by simp
      with strict_less win_count_other
      have less:
        "\<forall>x \<in> A-{a}. win_count q x < win_count q a"
        using DiffD1 antisym dual_order.trans
              not_le_imp_less win_count_a
        by metis
      hence
        "\<forall>x \<in> A-{a}. \<not>(\<forall>y \<in> A. win_count q y \<le> win_count q x)"
        using asm1 Profile.lifted_def not_le
        by metis
      hence
        "\<forall>x \<in> A-{a}.
          x \<notin> {a \<in> A. \<forall>x \<in> A. win_count q x \<le> win_count q a}"
        by blast
      hence
        "\<forall>x \<in> A-{a}. x \<notin> elect plurality A q"
        by simp
      moreover have
        "a \<in> elect plurality A q"
      proof -
        from less
        have
          "\<forall>x \<in> A-{a}. win_count q x \<le> win_count q a"
          using less_imp_le
          by metis
        moreover have
          "win_count q a \<le> win_count q a"
          by simp
        ultimately have
          "\<forall>x \<in> A. win_count q x \<le> win_count q a"
          by auto
        moreover have
          "a \<in> A"
          using a_in_win_p
          by auto
        ultimately have
          "a \<in> {a \<in> A.
              \<forall>x \<in> A. win_count q x \<le> win_count q a}"
          by auto
        thus ?thesis
          by simp
      qed
      moreover have
        "elect plurality A q \<subseteq> A"
        by simp
      ultimately show ?thesis
        by auto
    qed
  qed
qed

(*The plurality rule is invariant monotone.*)
theorem plurality_inv_mono[simp]: "invariant_monotonicity plurality"
proof -
  have
    "electoral_module plurality \<and>
      (\<forall>A p q a.
        (a \<in> elect plurality A p \<and> lifted A p q a) \<longrightarrow>
          (elect plurality A q = elect plurality A p \<or>
            elect plurality A q = {a}))"
  proof
    show "electoral_module plurality"
      by simp
  next
    show
      "\<forall>A p q a. (a \<in> elect plurality A p \<and> lifted A p q a) \<longrightarrow>
          (elect plurality A q = elect plurality A p \<or>
            elect plurality A q = {a})"
      using plurality_inv_mono2
      by metis
  qed
  thus ?thesis
    by (simp add: invariant_monotonicity_def)
qed

end
