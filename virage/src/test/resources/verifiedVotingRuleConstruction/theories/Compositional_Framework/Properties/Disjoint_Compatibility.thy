theory Disjoint_Compatibility
  imports "../Components/Electoral_Module"
          Indep_Of_Alt

begin

(*
   Two electoral modules are disjoint-compatible if they only make decisions
   over disjoint sets of alternatives. Electoral modules reject alternatives
   for which they make no decision.
*)
definition disjoint_compatibility :: "'a Electoral_Module \<Rightarrow>
                                         'a Electoral_Module \<Rightarrow> bool" where
  "disjoint_compatibility m n \<equiv>
    electoral_module m \<and> electoral_module n \<and>
        (\<forall>S. finite S \<longrightarrow>
          (\<exists>A \<subseteq> S.
            (\<forall>a \<in> A. indep_of_alt m S a \<and>
              (\<forall>p. finite_profile S p \<longrightarrow> a \<in> reject m S p)) \<and>
            (\<forall>a \<in> S-A. indep_of_alt n S a \<and>
              (\<forall>p. finite_profile S p \<longrightarrow> a \<in> reject n S p))))"

end