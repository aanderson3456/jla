import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real


set_option tactic.hygienic false

theorem page5_display3_equals2 (b:ℝ): 2^(b+1) * 4^(b-1) = 2^(3*b-1):=
/-
Formal verification of
https://arxiv.org/pdf/1408.2850.pdf
Page 5
3rd displayed equation
Second "equals" sign
-/
  (calc
  2^(3*b-1) = 2^(b+1 + 2*(b-1))     := by ring_nf
  _         = 2^(b+1) * 2^(2*(b-1)) := Real.rpow_add zero_lt_two _ _
  _         = 2^(b+1) * (2^2)^(b-1) := by rw [Real.rpow_mul zero_le_two _ _]
  _         = 2^(b+1) * 4^(b-1)     := by norm_num).symm


theorem page7_display4_lt2 (b c : ℝ) (h: b < c) :
2^(-b) + 2^(-c) < 2^(-(b-1)) :=
/-
Formal verification of
https://arxiv.org/pdf/1408.2850.pdf
Page 7
4th displayed equation
Second "<" sign
-/
  have : -c < -b         := neg_lt_neg h
  have : 2^(-c) < 2^(-b) := (Real.rpow_lt_rpow_left_iff one_lt_two).mpr this
  calc
  _ < 2^(-b) + 2^(-b) := (Real.add_lt_add_iff_left (2 ^ (-b))).mpr this
  _ = 2 * 2^(-b)      := by ring
  _ = 2^1 * 2^(-b)    := by rw [Real.rpow_one]
  _ = 2^(1+(-b))      := by rw [← Real.rpow_add zero_lt_two]
  _ = 2^(-(b-1))      := by ring_nf

/-
Page 8
5th displayed equation
Inequality
proved in paper_bound'' below
-/

theorem bound_of_nonneg (p:ℝ) : 0 ≤ 4*p*(p-1) + 1 := calc
  _ ≤ (2*p-1)*(2*p-1) := mul_self_nonneg _
  _ = 4*(p*p) - 4*p + 1 := by ring
  _ = _                 := by ring

theorem numerator_bound (p:ℝ) : 4*(p*(1-p)) ≤ 1 :=
  calc
  _ = - (4*p*(p-1))         := by ring
  _ = - (4*p*(p-1) + 1) + 1 := by ring
  _ ≤ -0 + 1                := add_le_add_right (neg_le_neg (bound_of_nonneg p)) 1
  _ = 1                     := by ring

theorem le_div {a b c : ℝ} (ha: 0<a) (g: a*b ≤ c) : b ≤ c/a :=
  ((le_div_iff' ha).mpr) g

theorem the_bound (p:ℝ) : p*(1-p) ≤ 1/4 :=
  le_div zero_lt_four (numerator_bound p)

theorem mul_self_bound {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) : p*p ≤ 1 := calc
_ ≤ p * 1 := mul_le_mul_of_nonneg_left h1 h0
_ ≤ 1 * 1 := mul_le_mul_of_nonneg_right h1 zero_le_one
_ = 1     := one_mul 1


theorem sq_bound {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) : p^2 ≤ 1 :=
  calc
  _ = p^(1+1)     := by ring_nf
  _ = p^(1) * p^1   := Real.rpow_add' h0 (by linarith)
  _ = p*p         := by rw [Real.rpow_one]
  _ ≤ 1           := mul_self_bound h0 h1


theorem cube_bound {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) : p^3 ≤ 1 :=
  calc
  _ = p^(2+1)     := by ring_nf
  _ = p^2 * p^1   := Real.rpow_add' h0 (by linarith)
  _ = p^2 * p     := by rw [Real.rpow_one]
  _ ≤ 1 * p       := mul_le_mul_of_nonneg_right (sq_bound h0 h1) (h0)
  _ = p           := one_mul _
  _ ≤ 1           := h1


theorem cube_bound' {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) : (1-p)^3 ≤ 1 :=
  cube_bound (sub_nonneg.mpr h1) (sub_le_self 1 h0)

theorem paper_bound {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) :
  (1-p)^3 + p^3 ≤ 2 := calc
  (1-p)^3 + p^3 ≤ (1-p)^3 + 1 := add_le_add_left  (cube_bound  h0 h1) _
  _             ≤ 1 + 1       := add_le_add_right (cube_bound' h0 h1) _
  _             = 2 := by ring


theorem paper_bound' {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) : p * (1-p) * ((1-p)^3 + p^3) ≤ 1/2 :=
calc
_ ≤ p * (1-p) * 2 := mul_le_mul_of_nonneg_left (paper_bound h0 h1) (mul_nonneg h0 (sub_nonneg.mpr h1)) 
_ ≤ (1/4) * 2     := mul_le_mul_of_nonneg_right (the_bound _) (by linarith)
_ = _             := by ring

theorem paper_bound'' {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) :
  (1-p)^4 * p + p^4 * (1-p) ≤ 1/2 :=
calc
  _ = (1-p)^(3+1) * p         + p^(3+1) * (1-p)     := by ring_nf
  _ = (1-p)^(3) * (1-p)^1 * p + (p^3 * p^1) * (1-p) := by {
      rw [Real.rpow_add',Real.rpow_add']
      exact h0; linarith; exact sub_nonneg.mpr h1; linarith
      --or a one-linear: rw [Real.rpow_add' (sub_nonneg.mpr h1) (by linarith),Real.rpow_add' h0 (by linarith)]
    }
  _ = (1-p)^(3) * (1-p)   * p + (p^3 * p) * (1-p)   := by rw [Real.rpow_one,Real.rpow_one]
  _ = p * (1-p) * ( (1-p)^(3) + p^3)                := by ring
  _ ≤ _                                             := paper_bound' h0 h1
