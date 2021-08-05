(*  File:       Pass_Module.thy
    Copyright   2021  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Karsten Diekhoff, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Jonas Kraemer, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Michael Kirsten, Karlsruhe Institute of Technology (KIT)"\<close>

section \<open>Pass Module\<close>

theory Pass_Module
  imports "../Electoral_Module"
begin

text
\<open>This is a family of electoral modules. For a natural number n and a
lexicon (linear order) r of all alternatives, the according pass module
defers the lexicographically first n alternatives (from A) and rejects
the rest. It is primarily used as counterpart to the drop module in a
parallel composition in order to segment the alternatives into two groups.\<close>

subsection \<open>Definition\<close>

fun pass_module :: "nat \<Rightarrow> 'a Preference_Relation \<Rightarrow> 'a Electoral_Module" where
  "pass_module n r A p =
    ({},
    {a \<in> A. card(above (limit A r) a) > n},
    {a \<in> A. card(above (limit A r) a) \<le> n})"

subsection \<open>Soundness\<close>

theorem pass_mod_sound[simp]:
  assumes order: "linear_order r"
  shows "electoral_module (pass_module n r)"
proof -
  let ?mod = "pass_module n r"
  have
    "\<forall> A p. finite_profile A p \<longrightarrow>
          (\<forall>a \<in> A. a \<in> {x \<in> A. card(above (limit A r) x) > n} \<or>
                   a \<in> {x \<in> A. card(above (limit A r) x) \<le> n})"
    using CollectI not_less
    by metis
  hence
    "\<forall> A p. finite_profile A p \<longrightarrow>
          {a \<in> A. card(above (limit A r) a) > n} \<union>
          {a \<in> A. card(above (limit A r) a) \<le> n} = A"
    by blast
  hence 0:
    "\<forall> A p. finite_profile A p \<longrightarrow> set_equals_partition A (pass_module n r A p)"
    by simp
  have
    "\<forall> A p. finite_profile A p \<longrightarrow>
      (\<forall>a \<in> A. \<not>(a \<in> {x \<in> A. card(above (limit A r) x) > n} \<and>
                 a \<in> {x \<in> A. card(above (limit A r) x) \<le> n}))"
    by auto
  hence
    "\<forall> A p. finite_profile A p \<longrightarrow>
      {a \<in> A. card(above (limit A r) a) > n} \<inter>
      {a \<in> A. card(above (limit A r) a) \<le> n} = {}"
    by blast
  hence 1:
    "\<forall> A p. finite_profile A p \<longrightarrow> disjoint3 (?mod A p)"
    by simp
  from 0 1
  have
    "\<forall> A p. finite_profile A p \<longrightarrow> well_formed A (?mod A p)"
    by simp
  hence
    "\<forall> A p. finite_profile A p \<longrightarrow> well_formed A (?mod A p)"
    by simp
  thus ?thesis
    using electoral_modI
    by metis
qed

end
