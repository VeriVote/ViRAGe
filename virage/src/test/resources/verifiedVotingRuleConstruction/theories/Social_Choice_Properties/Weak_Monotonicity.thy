theory Weak_Monotonicity
  imports "../Compositional_Framework/Components/Electoral_Module"

begin

(*
   An electoral module is monotone iff
   when an elected alternative is lifted, this alternative remains elected.
*)
definition monotonicity :: "'a Electoral_Module \<Rightarrow> bool" where
  "monotonicity m \<equiv>
    electoral_module m \<and>
      (\<forall>A p q w.
          (finite A \<and> w \<in> elect m A p \<and> lifted A p q w) \<longrightarrow> w \<in> elect m A q)"

end