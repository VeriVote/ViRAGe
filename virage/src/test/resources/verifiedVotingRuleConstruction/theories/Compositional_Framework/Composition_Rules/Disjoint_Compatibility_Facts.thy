theory Disjoint_Compatibility_Facts
  imports "../Properties/Disjoint_Compatibility"
          "../Components/Basic_Modules/Drop_Module"
          "../Components/Basic_Modules/Pass_Module"

begin

(*The pass and drop module are (disjoint-)compatible.*)
theorem drop_pass_disj_compat[simp]:
  assumes order: "linear_order r"
  shows "disjoint_compatibility (drop_module n r) (pass_module n r)"
  unfolding disjoint_compatibility_def
proof (safe)
  show "electoral_module (drop_module n r)"
    using order
    by simp
next
  show "electoral_module (pass_module n r)"
    using order
    by simp
next
  fix
    S :: "'a set"
  assume
    fin: "finite S"
  obtain
    p :: "'a Profile"
    where "finite_profile S p"
    using empty_iff empty_set fin profile_set
    by metis
  show
    "\<exists>A \<subseteq> S.
      (\<forall>a \<in> A. indep_of_alt (drop_module n r) S a \<and>
        (\<forall>p. finite_profile S p \<longrightarrow>
          a \<in> reject (drop_module n r) S p)) \<and>
      (\<forall>a \<in> S-A. indep_of_alt (pass_module n r) S a \<and>
        (\<forall>p. finite_profile S p \<longrightarrow>
          a \<in> reject (pass_module n r) S p))"
  proof
    have same_A:
      "\<forall>p q. (finite_profile S p \<and> finite_profile S q) \<longrightarrow>
        reject (drop_module n r) S p =
          reject (drop_module n r) S q"
      by auto
    let ?A = "reject (drop_module n r) S p"
    have "?A \<subseteq> S"
      by auto
    moreover have
      "(\<forall>a \<in> ?A. indep_of_alt (drop_module n r) S a)"
      using order
      by (simp add: indep_of_alt_def)
    moreover have
      "\<forall>a \<in> ?A. \<forall>p. finite_profile S p \<longrightarrow>
        a \<in> reject (drop_module n r) S p"
      by auto
    moreover have
      "(\<forall>a \<in> S-?A. indep_of_alt (pass_module n r) S a)"
      using order
      by (simp add: indep_of_alt_def)
    moreover have
      "\<forall>a \<in> S-?A. \<forall>p. finite_profile S p \<longrightarrow>
        a \<in> reject (pass_module n r) S p"
      by auto
    ultimately show
      "?A \<subseteq> S \<and>
        (\<forall>a \<in> ?A. indep_of_alt (drop_module n r) S a \<and>
          (\<forall>p. finite_profile S p \<longrightarrow>
            a \<in> reject (drop_module n r) S p)) \<and>
        (\<forall>a \<in> S-?A. indep_of_alt (pass_module n r) S a \<and>
          (\<forall>p. finite_profile S p \<longrightarrow>
            a \<in> reject (pass_module n r) S p))"
      by simp
  qed
qed

end