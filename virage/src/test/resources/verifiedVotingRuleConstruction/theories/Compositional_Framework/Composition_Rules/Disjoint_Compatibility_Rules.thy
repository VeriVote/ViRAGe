theory Disjoint_Compatibility_Rules
  imports "../Properties/Disjoint_Compatibility"
          "../Components/Compositional_Structures/Sequential_Composition"

begin

(*If m and n are disjoint compatible, so are n and m.*)
theorem disj_compat_comm[simp]:
  assumes compatible: "disjoint_compatibility m n"
  shows "disjoint_compatibility n m"
proof -
  have
    "\<forall>S. finite S \<longrightarrow>
        (\<exists>A \<subseteq> S.
          (\<forall>a \<in> A. indep_of_alt n S a \<and>
            (\<forall>p. finite_profile S p \<longrightarrow> a \<in> reject n S p)) \<and>
          (\<forall>a \<in> S-A. indep_of_alt m S a \<and>
            (\<forall>p. finite_profile S p \<longrightarrow> a \<in> reject m S p)))"
  proof
    fix
      S :: "'a set"
    obtain A where old_A:
      "finite S \<longrightarrow>
          (A \<subseteq> S \<and>
            (\<forall>a \<in> A. indep_of_alt m S a \<and>
              (\<forall>p. finite_profile S p \<longrightarrow> a \<in> reject m S p)) \<and>
            (\<forall>a \<in> S-A. indep_of_alt n S a \<and>
              (\<forall>p. finite_profile S p \<longrightarrow> a \<in> reject n S p)))"
      using compatible disjoint_compatibility_def
      by fastforce
    hence
      "finite S \<longrightarrow>
          (\<exists>A \<subseteq> S.
            (\<forall>a \<in> S-A. indep_of_alt n S a \<and>
              (\<forall>p. finite_profile S p \<longrightarrow> a \<in> reject n S p)) \<and>
            (\<forall>a \<in> A. indep_of_alt m S a \<and>
              (\<forall>p. finite_profile S p \<longrightarrow> a \<in> reject m S p)))"
      by auto
    hence
      "finite S \<longrightarrow>
          (\<exists>A \<subseteq> S.
            (\<forall>a \<in> S-A. indep_of_alt n S a \<and>
              (\<forall>p. finite_profile S p \<longrightarrow> a \<in> reject n S p)) \<and>
            (\<forall>a \<in> S-(S-A). indep_of_alt m S a \<and>
              (\<forall>p. finite_profile S p \<longrightarrow> a \<in> reject m S p)))"
      using double_diff order_refl
      by metis
    thus
      "finite S \<longrightarrow>
          (\<exists>A \<subseteq> S.
            (\<forall>a \<in> A. indep_of_alt n S a \<and>
              (\<forall>p. finite_profile S p \<longrightarrow> a \<in> reject n S p)) \<and>
            (\<forall>a \<in> S-A. indep_of_alt m S a \<and>
              (\<forall>p. finite_profile S p \<longrightarrow> a \<in> reject m S p)))"
      by fastforce
  qed
  moreover have "electoral_module m \<and> electoral_module n"
    using compatible disjoint_compatibility_def
    by auto
  ultimately show ?thesis
    by (simp add: disjoint_compatibility_def)
qed

(*
   Sequentially composing electoral modules after compatible
   electoral modules does not break their compatibility.
*)
theorem disj_compat_seq[simp]:
  assumes
    compatible: "disjoint_compatibility m n" and
    module_m2: "electoral_module m2"
  shows "disjoint_compatibility (sequential_composition m m2) n"
  unfolding disjoint_compatibility_def
proof (safe)
  show "electoral_module (m \<triangleright> m2)"
    using compatible disjoint_compatibility_def module_m2 seq_comp_sound
    by metis
next
  show "electoral_module n"
    using compatible disjoint_compatibility_def
    by metis
next
  fix
    S :: "'a set"
  assume
    fin_S: "finite S"
  have modules:
    "electoral_module (m \<triangleright> m2) \<and> electoral_module n"
    using compatible disjoint_compatibility_def module_m2 seq_comp_sound
    by metis
  obtain A where A:
    "A \<subseteq> S \<and>
      (\<forall>a \<in> A. indep_of_alt m S a \<and>
        (\<forall>p. finite_profile S p \<longrightarrow> a \<in> reject m S p)) \<and>
      (\<forall>a \<in> S-A. indep_of_alt n S a \<and>
        (\<forall>p. finite_profile S p \<longrightarrow> a \<in> reject n S p))"
    using compatible disjoint_compatibility_def fin_S
    by (metis (no_types, lifting))
  show
    "\<exists>A \<subseteq> S.
      (\<forall>a \<in> A. indep_of_alt (m \<triangleright> m2) S a \<and>
        (\<forall>p. finite_profile S p \<longrightarrow> a \<in> reject (m \<triangleright> m2) S p)) \<and>
      (\<forall>a \<in> S-A. indep_of_alt n S a \<and>
        (\<forall>p. finite_profile S p \<longrightarrow> a \<in> reject n S p))"
  proof
    have
      "\<forall>a p q.
        a \<in> A \<and> equiv_prof_except_a S p q a \<longrightarrow>
          (m \<triangleright> m2) S p = (m \<triangleright> m2) S q"
    proof (safe)
      fix
        a :: "'a" and
        p :: "'a Profile" and
        q :: "'a Profile"
      assume
        a: "a \<in> A" and
        b: "equiv_prof_except_a S p q a"
      have eq_def:
        "defer m S p = defer m S q"
        using A a b indep_of_alt_def
        by metis
      from a b have profiles:
        "finite_profile S p \<and> finite_profile S q"
        using equiv_prof_except_a_def
        by fastforce
      hence "(defer m S p) \<subseteq> S"
        using compatible defer_in_alts disjoint_compatibility_def
        by blast
      hence
        "limit_profile (defer m S p) p =
          limit_profile (defer m S q) q"
        using A DiffD2 a b compatible defer_not_elec_or_rej
              disjoint_compatibility_def eq_def profiles
              negl_diff_imp_eq_limit_prof
        by (metis (no_types, lifting))
      with eq_def have
        "m2 (defer m S p) (limit_profile (defer m S p) p) =
          m2 (defer m S q) (limit_profile (defer m S q) q)"
        by simp
      moreover have "m S p = m S q"
        using A a b indep_of_alt_def
        by metis
      ultimately show
        "(m \<triangleright> m2) S p = (m \<triangleright> m2) S q"
        using sequential_composition.simps
        by (metis (full_types))
    qed
    moreover have
      "\<forall>a \<in> A. \<forall>p. finite_profile S p \<longrightarrow> a \<in> reject (m \<triangleright> m2) S p"
      using A UnI1 prod.sel sequential_composition.simps
      by metis
    ultimately show
      "A \<subseteq> S \<and>
        (\<forall>a \<in> A. indep_of_alt (m \<triangleright> m2) S a \<and>
          (\<forall>p. finite_profile S p \<longrightarrow> a \<in> reject (m \<triangleright> m2) S p)) \<and>
        (\<forall>a \<in> S-A. indep_of_alt n S a \<and>
          (\<forall>p. finite_profile S p \<longrightarrow> a \<in> reject n S p))"
      using A indep_of_alt_def modules
      by (metis (mono_tags, lifting))
  qed
qed

end