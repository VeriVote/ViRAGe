(*  File:       Revision_Composition.thy
    Copyright   2021  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Karsten Diekhoff, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Jonas Kraemer, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Michael Kirsten, Karlsruhe Institute of Technology (KIT)"\<close>

section \<open>Revision Composition\<close>

theory Revision_Composition
  imports "../Electoral_Module"
begin

text
\<open>A revised electoral module rejects all originally rejected or deferred
alternatives, and defers the originally elected alternatives.
It does not elect any alternatives.\<close>

subsection \<open>Definition\<close>

fun revision_composition :: "'a Electoral_Module \<Rightarrow> 'a Electoral_Module" where
  "revision_composition m A p = ({}, A - elect m A p, elect m A p)"

abbreviation rev ::
"'a Electoral_Module \<Rightarrow> 'a Electoral_Module" ("_\<down>" 50) where
  "m\<down> == revision_composition m"

subsection \<open>Soundness\<close>

theorem rev_comp_sound[simp]:
  assumes module: "electoral_module m"
  shows "electoral_module (revision_composition m)"
proof -
  from module have "\<forall>A p. finite_profile A p \<longrightarrow> elect m A p \<subseteq> A"
    using elect_in_alts
    by auto
  hence "\<forall>A p. finite_profile A p \<longrightarrow> (A - elect m A p) \<union> elect m A p = A"
    by blast
  hence unity:
    "\<forall>A p. finite_profile A p \<longrightarrow>
      set_equals_partition A (revision_composition m A p)"
    by simp
  have "\<forall>A p. finite_profile A p \<longrightarrow> (A - elect m A p) \<inter> elect m A p = {}"
    by blast
  hence disjoint:
    "\<forall>A p. finite_profile A p \<longrightarrow> disjoint3 (revision_composition m A p)"
    by simp
  from unity disjoint show ?thesis
    by (simp add: electoral_modI)
qed

subsection \<open>Composition Rules\<close>





end
