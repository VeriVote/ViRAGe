(*  File:       Sequential_Majority_Comparison.thy
    Copyright   2021  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Karsten Diekhoff, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Jonas Kraemer, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Michael Kirsten, Karlsruhe Institute of Technology (KIT)"\<close>

section \<open>Sequential Majority Comparison\<close>

theory Sequential_Majority_Comparison
  imports "../Compositional_Framework/Components/Basic_Modules/Plurality_Module"
          "../Compositional_Framework/Components/Basic_Modules/Pass_Module"
          "../Compositional_Framework/Components/Basic_Modules/Drop_Module"
          "../Compositional_Framework/Components/Compositional_Structures/Revision_Composition"
          "../Compositional_Framework/Components/Composites/Composite_Structures"
          "../Compositional_Framework/Composition_Rules/Monotonicity_Rules"
          "../Compositional_Framework/Composition_Rules/Result_Rules"
          "../Compositional_Framework/Composition_Rules/Disjoint_Compatibility_Facts"
          "../Compositional_Framework/Composition_Rules/Disjoint_Compatibility_Rules"

begin

text
\<open>Sequential majority comparison compares two alternatives by plurality voting.
The loser gets rejected, and the winner is compared to the next alternative.
This process is repeated until only a single alternative is left, which is
then elected.\<close>

subsection \<open>Definition\<close>

fun smc :: "'a Preference_Relation \<Rightarrow> 'a Electoral_Module" where
  "smc x A p =
      ((((((pass_module 2 x) \<triangleright> ((plurality\<down>) \<triangleright> (pass_module 1 x))) \<parallel>\<^sub>\<up>
      (drop_module 2 x)) \<circlearrowleft>\<^sub>\<exists>\<^sub>!\<^sub>d) \<triangleright> elect_module) A p)"

end
