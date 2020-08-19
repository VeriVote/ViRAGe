theory blacks_rule
imports borda_module elect_module condorcet_module

begin

(*************************************)
(*** Definition: Black Voting Rule ***)
(*************************************)

definition Black :: "'a Electoral_module" where
  "Black \<equiv> Condorcet_Nonelecting \<triangleright> Borda"

definition Black_code :: "'a Electoral_module" where
  "Black_code \<equiv> Condorcet_Nonelecting_code \<triangleright> Borda_code"

export_code Black_code in Haskell

end