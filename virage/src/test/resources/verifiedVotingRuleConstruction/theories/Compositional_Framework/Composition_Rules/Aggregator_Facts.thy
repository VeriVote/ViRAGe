theory Aggregator_Facts
  imports "../Properties/Aggregator_Properties"
          "../Components/Basic_Modules/Maximum_Aggregator"

begin

(*The max-aggregator is commutative.*)
theorem max_agg_comm[simp]: "agg_commutative max_aggregator"
  unfolding agg_commutative_def
proof (safe)
  show "aggregator max_aggregator"
    by simp
next
  fix
    A :: "'a set" and
    e1 :: "'a set" and
    e2 :: "'a set" and
    d1 :: "'a set" and
    d2 :: "'a set" and
    r1 :: "'a set" and
    r2 :: "'a set"
  show
    "max_aggregator A (e1, r1, d1) (e2, r2, d2) =
      max_aggregator A (e2, r2, d2) (e1, r1, d1)"
  by auto
qed


(*The max-aggregator is conservative.*)
theorem max_agg_consv[simp]: "agg_conservative max_aggregator"
proof -
  have
    "\<forall>A e1 e2 d1 d2 r1 r2.
          (well_formed A (e1, r1, d1) \<and> well_formed A (e2, r2, d2)) \<longrightarrow>
      reject_r (max_aggregator A (e1, r1, d1) (e2, r2, d2)) = r1 \<inter> r2"
    using max_agg_rej_set
    by blast
  hence
    "\<forall>A e1 e2 d1 d2 r1 r2.
            (well_formed A (e1, r1, d1) \<and> well_formed A (e2, r2, d2)) \<longrightarrow>
        reject_r (max_aggregator A (e1, r1, d1) (e2, r2, d2)) \<subseteq> r1 \<inter> r2"
    by blast
  moreover have
    "\<forall>A e1 e2 d1 d2 r1 r2.
        (well_formed A (e1, r1, d1) \<and> well_formed A (e2, r2, d2)) \<longrightarrow>
            elect_r (max_aggregator A (e1, r1, d1) (e2, r2, d2)) \<subseteq> (e1 \<union> e2)"
    by (simp add: subset_eq)
  ultimately have
    "\<forall>A e1 e2 d1 d2 r1 r2.
        (well_formed A (e1, r1, d1) \<and> well_formed A (e2, r2, d2)) \<longrightarrow>
            (elect_r (max_aggregator A (e1, r1, d1) (e2, r2, d2)) \<subseteq> (e1 \<union> e2) \<and>
             reject_r (max_aggregator A (e1, r1, d1) (e2, r2, d2)) \<subseteq> (r1 \<union> r2))"
    by blast
  moreover have
    "\<forall>A e1 e2 d1 d2 r1 r2.
        (well_formed A (e1, r1, d1) \<and> well_formed A (e2, r2, d2)) \<longrightarrow>
            defer_r (max_aggregator A (e1, r1, d1) (e2, r2, d2)) \<subseteq> (d1 \<union> d2)"
    by auto
  ultimately have
    "\<forall>A e1 e2 d1 d2 r1 r2.
        (well_formed A (e1, r1, d1) \<and> well_formed A (e2, r2, d2)) \<longrightarrow>
            (elect_r (max_aggregator A (e1, r1, d1) (e2, r2, d2)) \<subseteq> (e1 \<union> e2) \<and>
            reject_r (max_aggregator A (e1, r1, d1) (e2, r2, d2)) \<subseteq> (r1 \<union> r2) \<and>
            defer_r (max_aggregator A (e1, r1, d1) (e2, r2, d2)) \<subseteq> (d1 \<union> d2))"
    by blast
  thus ?thesis
    by (simp add: agg_conservative_def)
qed

end