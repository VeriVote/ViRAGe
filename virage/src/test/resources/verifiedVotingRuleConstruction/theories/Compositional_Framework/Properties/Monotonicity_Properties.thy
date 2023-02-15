theory Monotonicity_Properties
  imports "../Components/Electoral_Module"
          Result_Properties

begin

(*
   An electoral module is defer-lift-invariant iff
   lifting a deferred alternative does not affect the outcome.
*)
definition defer_lift_invariance :: "'a Electoral_Module \<Rightarrow> bool" where
  "defer_lift_invariance m \<equiv>
    electoral_module m \<and>
      (\<forall>A p q a.
          (a \<in> (defer m A p) \<and> lifted A p q a) \<longrightarrow> m A p = m A q)"

(*
   Lifting an elected alternative a from an invariant-monotone
   electoral module either does not change the elect set, or
   makes a the only elected alternative.
*)
definition invariant_monotonicity :: "'a Electoral_Module \<Rightarrow> bool" where
  "invariant_monotonicity m \<equiv>
    electoral_module m \<and>
        (\<forall>A p q a. (a \<in> elect m A p \<and> lifted A p q a) \<longrightarrow>
          (elect m A q = elect m A p \<or> elect m A q = {a}))"

(*
   Lifting a deferred alternative a from a defer-invariant-monotone
   electoral module either does not change the defer set, or
   makes a the only deferred alternative.
*)
definition defer_invariant_monotonicity :: "'a Electoral_Module \<Rightarrow> bool" where
  "defer_invariant_monotonicity m \<equiv>
    electoral_module m \<and> non_electing m \<and>
        (\<forall>A p q a. (a \<in> defer m A p \<and> lifted A p q a) \<longrightarrow>
          (defer m A q = defer m A p \<or> defer m A q = {a}))"

(*
   An electoral module is defer-monotone iff,
   when a deferred alternative is lifted, this alternative remains deferred.
*)
definition defer_monotonicity :: "'a Electoral_Module \<Rightarrow> bool" where
  "defer_monotonicity m \<equiv>
    electoral_module m \<and>
      (\<forall>A p q w.
          (finite A \<and> w \<in> defer m A p \<and> lifted A p q w) \<longrightarrow> w \<in> defer m A q)"


end