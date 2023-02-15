(*  File:       Minimax_Rule.thy
    Copyright   2021  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Stephan Bohr, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Michael Kirsten, Karlsruhe Institute of Technology (KIT)"\<close>

section \<open>Minimax Rule\<close>

theory Minimax_Rule
  imports "Compositional_Structures/Basic_Modules/Minimax_Module"
          "Compositional_Structures/Elect_Composition"
begin

text
\<open>This is the Minimax voting rule. It elects the alternatives with the highest
Minimax score.\<close>

subsection \<open>Definition\<close>

fun minimax_rule :: "'a Electoral_Module" where
  "minimax_rule A p = elector minimax A p"

fun minimax_rule_code :: "'a Electoral_Module" where
  "minimax_rule_code A p = elector minimax_code A p"

subsection \<open>Condorcet Consistency Property\<close>

theorem minimax_condorcet: "condorcet_consistency minimax_rule"
proof -
  have
    "condorcet_consistency (elector minimax)"
    using minimax_is_dcc dcc_imp_cc_elector
    by metis
  thus ?thesis
    using condorcet_consistency2 electoral_module_def
          minimax_rule.simps
    by metis
qed

end
