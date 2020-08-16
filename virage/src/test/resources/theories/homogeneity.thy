theory homogeneity
imports electoral_modules

begin

(*************************************************)
(*** Homogeneity related definitions ***)
(*************************************************)

abbreviation times :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"times n l \<equiv> concat (replicate n l)"


definition homogeneous :: "'a Electoral_module \<Rightarrow> bool" where
"homogeneous m \<equiv> electoral_module m \<and> (
    \<forall> A p n . (finite_profile A p \<and> n > 0 \<longrightarrow> (
      m A p = m A (times n p))))"

end