theory Aggregator_Properties
  imports "../Components/Aggregator"

begin

definition agg_commutative :: "'a Aggregator \<Rightarrow> bool" where
  "agg_commutative agg \<equiv>
    aggregator agg \<and> (\<forall>A e1 e2 d1 d2 r1 r2.
      agg A (e1, r1, d1) (e2, r2, d2) = agg A (e2, r2, d2) (e1, r1, d1))"

definition agg_conservative :: "'a Aggregator \<Rightarrow> bool" where
  "agg_conservative agg \<equiv>
    aggregator agg \<and>
    (\<forall>A e1 e2 d1 d2 r1 r2.
      ((well_formed A (e1, r1, d1) \<and> well_formed A (e2, r2, d2)) \<longrightarrow>
        elect_r (agg A (e1, r1, d1) (e2, r2, d2)) \<subseteq> (e1 \<union> e2) \<and>
        reject_r (agg A (e1, r1, d1) (e2, r2, d2)) \<subseteq> (r1 \<union> r2) \<and>
        defer_r (agg A (e1, r1, d1) (e2, r2, d2)) \<subseteq> (d1 \<union> d2)))"

end