(*  File:       Plurality_Module.thy
    Copyright   2021  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Karsten Diekhoff, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Jonas Kraemer, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Michael Kirsten, Karlsruhe Institute of Technology (KIT)"\<close>

section \<open>Plurality Module\<close>

theory Plurality_Module
  imports "../Electoral_Module"
begin

text
\<open>The plurality module implements the plurality voting rule.
The plurality rule elects all modules with the maximum amount of top
preferences among all alternatives, and rejects all the other alternatives.
It is electing and induces the classical plurality (voting) rule
from social-choice theory.\<close>

subsection \<open>Definition\<close>

fun plurality :: "'a Electoral_Module" where
  "plurality A p =
    ({a \<in> A. \<forall>x \<in> A. win_count p x \<le> win_count p a},
     {a \<in> A. \<exists>x \<in> A. win_count p x > win_count p a},
     {})"

subsection \<open>Soundness\<close>

theorem plurality_sound[simp]: "electoral_module plurality"
proof -
  have
    "\<forall>A p.
      let elect = {a \<in> (A::'a set). \<forall>x \<in> A. win_count p x \<le> win_count p a};
      reject = {a \<in> A. \<exists>x \<in> A. win_count p x > win_count p a} in
    elect \<inter> reject = {}"
    by auto
  hence disjoint:
    "\<forall>A p.
      let elect = {a \<in> (A::'a set). \<forall>x \<in> A. win_count p x \<le> win_count p a};
      reject = {a \<in> A. \<exists>x \<in> A. win_count p x > win_count p a} in
    disjoint3 (elect, reject, {})"
    by simp
  have
    "\<forall>A p.
      let elect = {a \<in> (A::'a set). \<forall>x \<in> A. win_count p x \<le> win_count p a};
      reject = {a \<in> A. \<exists>x \<in> A. win_count p x > win_count p a} in
    elect \<union> reject = A"
    using not_le_imp_less
    by auto
  hence unity:
    "\<forall>A p.
      let elect = {a \<in> (A::'a set). \<forall>x \<in> A. win_count p x \<le> win_count p a};
      reject = {a \<in> A. \<exists>x \<in> A. win_count p x > win_count p a} in
    set_equals_partition A (elect, reject, {})"
    by simp
  from disjoint unity show ?thesis
    by (simp add: electoral_modI)
qed

end
