(*  File:       Evaluation_Function.thy
    Copyright   2021  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Stephan Bohr, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Michael Kirsten, Karlsruhe Institute of Technology (KIT)"\<close>

section \<open>Evaluation Function\<close>

theory Evaluation_Function
  imports "../../Social_Choice_Types/Profile"
begin

text
\<open>This is the evaluation function. From a set of currently eligible alternatives,
the evaluation function computes a numerical value that is then to be used for
further (s)election, e.g., by the elimination module.\<close>

subsection \<open>Definition\<close>

type_synonym 'a Evaluation_Function = "'a  \<Rightarrow> 'a set \<Rightarrow> 'a Profile \<Rightarrow> nat"

end
