(*  Title:      HOL/Examples/Generalized_effective_completeness_for_continuous_logic.thy
    Author:     Bjørn Kjos-Hanssen
*)

section ‹Caleb Camrud JLA 2023›

theory Generalized_effective_completeness_for_continuous_logic
  imports Main HOL.Real
begin
(*
This article by Caleb Camrud mentions the density of the dyadic rationals in the reals.
We merely prove the density of the rationals in the reals.
*)

lemma real_dense : "∀x::real. ∀y::real. (x < y ⟶ (∃z::real. x < z ∧ z < y))"
  using dense by blast

lemma rat_dense_in_real : "∀x::real. ∀y::real. (x < y ⟶ (∃z::rat. x < real_of_rat(z) ∧ real_of_rat(z) < y))"
  using of_rat_dense by blast
    
end
