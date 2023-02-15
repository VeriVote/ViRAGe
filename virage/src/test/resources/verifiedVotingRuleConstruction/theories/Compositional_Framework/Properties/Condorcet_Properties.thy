theory Condorcet_Properties
  imports "../Components/Electoral_Module"
          "../Components/Evaluation_Function"

begin

definition condorcet_compatibility :: "'a Electoral_Module \<Rightarrow> bool" where
  "condorcet_compatibility m \<equiv>
    electoral_module m \<and>
    (\<forall> A p w. condorcet_winner A p w \<and> finite A \<longrightarrow>
      (w \<notin> reject m A p \<and>
        (\<forall>l. \<not>condorcet_winner A p l \<longrightarrow> l \<notin> elect m A p) \<and>
          (w \<in> elect m A p \<longrightarrow>
            (\<forall>l. \<not>condorcet_winner A p l \<longrightarrow> l \<in> reject m A p))))"

(*
   An Evaluation function is Condorcet-rating iff the following holds:
   If a Condorcet Winner w exists, w and only w has the highest value.
*)
definition condorcet_rating :: "'a Evaluation_Function \<Rightarrow> bool" where
  "condorcet_rating f \<equiv>
    \<forall>A p w . condorcet_winner A p w \<longrightarrow>
      (\<forall>l \<in> A . l \<noteq> w \<longrightarrow> f l A p < f w A p)"

definition defer_condorcet_consistency :: "'a Electoral_Module \<Rightarrow> bool" where
  "defer_condorcet_consistency m \<equiv>
    electoral_module m \<and>
    (\<forall> A p w. condorcet_winner A p w \<and> finite A \<longrightarrow>
      (m A p =
        ({},
        A - (defer m A p),
        {d \<in> A. condorcet_winner A p d})))"

end