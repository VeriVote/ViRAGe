theory Homogeneity
  imports "../Compositional_Framework/Components/Electoral_Module"

begin 

fun times :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "times n l = concat (replicate n l)"

definition homogeneity :: "'a Electoral_Module \<Rightarrow> bool" where
"homogeneity m \<equiv>
  electoral_module m \<and>
    (\<forall> A p n .
      (finite_profile A p \<and> n > 0 \<longrightarrow>
          (m A p = m A (times n p))))"

end