(*  Title:      HOL/Examples/Generalized_effective_completeness_for_continuous_logic.thy
    Author:     Bjørn Kjos-Hanssen
*)

section ‹Caleb Camrud JLA 2023›

theory Generalized_effective_completeness_for_continuous_logic
  imports Main HOL.Real
begin
(*
On page 6 this article by Caleb Camrud mentions the density of the dyadic rationals in the unit interval of the reals.
We merely prove (by automation) the density of the rationals in the reals,
and then more elaborately the density of the rationals Q in [0,1].
*)

lemma real_dense : "∀x::real. ∀y::real. (x < y ⟶ (∃z::real. x < z ∧ z < y))"
  using dense by blast

lemma rat_dense_in_real : "∀x::real. ∀y::real. (x < y ⟶ (∃z::rat. x < real_of_rat(z) ∧ real_of_rat(z) < y))"
  by (simp add: of_rat_dense)

lemma rat_dense_in_real_unit : "∀x::real. ∀y::real. (
  (x < y ∧  (0 ≤ x ∧ x ≤ 1) ∧  (0 ≤ y ∧ y ≤ 1))  ⟶
  (∃z::rat.(0 ≤ real_of_rat(z) ∧ real_of_rat(z) ≤ 1) ∧ x < real_of_rat(z) ∧ real_of_rat(z) < y)
)"
proof
  fix a::real
  show " ∀y::real. (
  (a < y ∧  (0 ≤ a ∧ a ≤ 1) ∧  (0 ≤ y ∧ y ≤ 1))  ⟶
  (∃z::rat.(0 ≤ real_of_rat(z) ∧ real_of_rat(z) ≤ 1) ∧ a < real_of_rat(z) ∧ real_of_rat(z) < y)
)"
  proof
    fix b::real
    show "(a < b ∧  (0 ≤ a ∧ a ≤ 1) ∧  (0 ≤ b ∧ b ≤ 1))  ⟶
  (∃z::rat.(0 ≤ real_of_rat(z) ∧ real_of_rat(z) ≤ 1) ∧ a < real_of_rat(z) ∧ real_of_rat(z) < b)"
    proof
      assume hab : " (a < b ∧ (0 ≤ a ∧ a ≤ 1) ∧ (0 ≤ b ∧ b ≤ 1))"
      show " (∃z::rat.(0 ≤ real_of_rat(z) ∧ real_of_rat(z) ≤ 1) ∧ a < real_of_rat(z) ∧ real_of_rat(z) < b)"
      proof - (* The dash is crucial *)
        from rat_dense_in_real have
          "∀y::real. (a < y ⟶ (∃z::rat. a < real_of_rat(z) ∧ real_of_rat(z) < y))" ..
        then have
          hdense : "(a < b ⟶ (∃z::rat. a < real_of_rat(z) ∧ real_of_rat(z) < b))" ..
        from hab have hab1 : "a < b" ..
        from hdense and hab1 have
          "(∃z::rat. a < real_of_rat(z) ∧ real_of_rat(z) < b)" by (rule mp)  
        then obtain q where
          hq : " a < real_of_rat(q) ∧ real_of_rat(q) < b" by (rule exE)
        from hab and hq  have
          "(0 ≤ real_of_rat(q) ∧ real_of_rat(q) ≤ 1) ∧ (a < real_of_rat(q) ∧ real_of_rat(q) < b)" by linarith
        then
        have "(∃ z :: rat . (0 ≤ real_of_rat(z) ∧ real_of_rat(z) ≤ 1) ∧ (a < real_of_rat(z) ∧ real_of_rat(z) < b))" ..
        thus "(∃ z :: rat . (0 ≤ real_of_rat(z) ∧ real_of_rat(z) ≤ 1) ∧ (a < real_of_rat(z) ∧ real_of_rat(z) < b))".
      qed
    qed
  qed
qed

end
