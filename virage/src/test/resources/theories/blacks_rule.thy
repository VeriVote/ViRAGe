theory blacks_rule
imports borda_module elect_module condorcet_module

begin

(*************************************)
(*** Definition: Black Voting Rule ***)
(*************************************)

definition Black :: "'a Electoral_module" where
  "Black \<equiv> Condorcet_Nonelecting \<triangleright> Borda"

end