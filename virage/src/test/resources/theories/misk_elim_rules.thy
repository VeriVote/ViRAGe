theory misk_elim_rules

imports  loop_composition defer_eq_condition elect_module elim_module sequential_composition

begin

(* Copelands SCF *) (* outdatet*)

(*

abbreviation wins :: "'a \<Rightarrow> 'a Profile \<Rightarrow> 'a \<Rightarrow> bool" where
  "wins x p y \<equiv> prefer_count p x y > prefer_count p y x"

fun C_Copeland_score :: "'a Eval_function" where
  "C_Copeland_score x A p = card{y | y . y \<in> A \<and> wins x p y} - card{y | y . y \<in> A \<and> wins y p x}"

definition Copeland :: "'a Electoral_module" where
  "Copeland \<equiv> let t = Defer_eq_condition 1 in
    ((Elimination_module C_Copeland_score) \<circlearrowleft>\<^sub>t) \<triangleright> Elect_module"

(* Minimax SCF *)

fun F_Minimax_score :: "'a Eval_function" where
  "F_Minimax_score x A p = Min {prefer_count p x y | y. y \<in> A-{x}}"

definition Minimax :: "'a Electoral_module" where
  "Minimax \<equiv> let t = Defer_eq_condition 1 in
    ((Elimination_module F_Minimax_score) \<circlearrowleft>\<^sub>t) \<triangleright> Elect_module"

*)

end