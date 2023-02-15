theory Indep_Of_Alt
  imports "../Components/Electoral_Module"

begin

(*
   An electoral module is independent of an alternative a iff
   a's ranking does not influence the outcome.
*)
definition indep_of_alt :: "'a Electoral_Module \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> bool" where
  "indep_of_alt m A a \<equiv>
    electoral_module m \<and> (\<forall>p q. equiv_prof_except_a A p q a \<longrightarrow> m A p = m A q)"

end