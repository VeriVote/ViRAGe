(*  File:       Drop_Module.thy
    Copyright   2021  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Karsten Diekhoff, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Jonas Kraemer, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Michael Kirsten, Karlsruhe Institute of Technology (KIT)"\<close>

section \<open>Drop Module\<close>

theory Drop_Module
  imports "../Electoral_Module"
begin

text
\<open>This is a family of electoral modules. For a natural number n and a
lexicon (linear order) r of all alternatives, the according drop module
rejects the lexicographically first n alternatives (from A) and
defers the rest.
It is primarily used as counterpart to the pass module in a
parallel composition, in order to segment the alternatives into
two groups.\<close>

subsection \<open>Definition\<close>

fun drop_module :: "nat \<Rightarrow> 'a Preference_Relation \<Rightarrow> 'a Electoral_Module" where
  "drop_module n r A p =
    ({},
    {a \<in> A. card(above (limit A r) a) \<le> n},
    {a \<in> A. card(above (limit A r) a) > n})"

subsection \<open>Soundness\<close>

theorem drop_mod_sound[simp]:
  assumes order: "linear_order r"
  shows "electoral_module (drop_module n r)"
proof -
  let ?mod = "drop_module n r"
  have
    "\<forall>A p. finite_profile A p \<longrightarrow>
        (\<forall>a \<in> A. a \<in> {x \<in> A. card(above (limit A r) x) \<le> n} \<or>
            a \<in> {x \<in> A. card(above (limit A r) x) > n})"
    by auto
  hence
    "\<forall>A p. finite_profile A p \<longrightarrow>
        {a \<in> A. card(above (limit A r) a) \<le> n} \<union>
        {a \<in> A. card(above (limit A r) a) > n} = A"
    by blast
  hence 0:
    "\<forall>A p. finite_profile A p \<longrightarrow>
        set_equals_partition A (drop_module n r A p)"
    by simp
  have
    "\<forall>A p. finite_profile A p \<longrightarrow>
        (\<forall>a \<in> A. \<not>(a \<in> {x \<in> A. card(above (limit A r) x) \<le> n} \<and>
            a \<in> {x \<in> A. card(above (limit A r) x) > n}))"
    by auto
  hence
    "\<forall>A p. finite_profile A p \<longrightarrow>
        {a \<in> A. card(above (limit A r) a) \<le> n} \<inter>
        {a \<in> A. card(above (limit A r) a) > n} = {}"
    by blast
  hence 1: "\<forall>A p. finite_profile A p \<longrightarrow> disjoint3 (?mod A p)"
    by simp
  from 0 1 have
    "\<forall>A p. finite_profile A p \<longrightarrow>
        well_formed A (?mod A p)"
    by simp
  hence
    "\<forall>A p. finite_profile A p \<longrightarrow>
        well_formed A (?mod A p)"
    by simp
  thus ?thesis
    using electoral_modI
    by metis
qed

end
