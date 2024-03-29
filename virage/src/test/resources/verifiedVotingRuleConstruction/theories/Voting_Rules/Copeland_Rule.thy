(*  File:       Copeland_Rule.thy
    Copyright   2021  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Stephan Bohr, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Michael Kirsten, Karlsruhe Institute of Technology (KIT)"\<close>

section \<open>Copeland Rule\<close>

theory Copeland_Rule
  imports "../Compositional_Framework/Components/Composites/Composite_Elimination_Modules"
          "../Compositional_Framework/Components/Composites/Composite_Structures"
          "../Compositional_Framework/Composition_Rules/Condorcet_Facts"

begin

text
\<open>This is the Copeland voting rule. The idea is to elect the alternatives with
the highest difference between the amount of simple-majority wins and the
amount of simple-majority losses.\<close>

subsection \<open>Definition\<close>

fun copeland_rule :: "'a Electoral_Module" where
  "copeland_rule A p = elector copeland A p"


theorem copeland_condorcet: "condorcet_consistency copeland_rule"
proof -
  have
    "condorcet_consistency (elector copeland)"
    using copeland_is_dcc dcc_imp_cc_elector
    by metis
  thus ?thesis
    using condorcet_consistency2 electoral_module_def
          copeland_rule.simps
    by metis
qed

end
