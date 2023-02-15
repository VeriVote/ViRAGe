theory Condorcet_Consistency
  imports "../Compositional_Framework/Components/Electoral_Module"

begin

definition condorcet_consistency :: "'a Electoral_Module \<Rightarrow> bool" where
  "condorcet_consistency m \<equiv>
    electoral_module m \<and>
    (\<forall> A p w. condorcet_winner A p w \<longrightarrow>
      (m A p =
        ({e \<in> A. condorcet_winner A p e},
          A - (elect m A p),
          {})))"

end