import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

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
uses the fact that p*(1-p)≤ 1/4 which we prove here:
-/

theorem bound_of_nonneg (x:ℝ) : 0 ≤ 4*x*(x-1) + 1 := calc
  _ ≤ (2*x-1)*(2*x-1) := mul_self_nonneg _
  _ = 4*(x*x) - 4*x + 1 := by ring
  _ = _                 := by ring

theorem numerator_bound (x:ℝ) : 4*(x*(1-x)) ≤ 1 :=
  calc
  _ = - (4*x*(x-1))         := by ring
  _ = - (4*x*(x-1) + 1) + 1 := by ring
  _ ≤ -0 + 1                := add_le_add_right (neg_le_neg (bound_of_nonneg x)) 1
  _ = 1                     := by ring

theorem le_div {a b c : ℝ} (ha: 0<a) (g: a*b ≤ c) : b ≤ c/a :=
  ((le_div_iff' ha).mpr) g

theorem the_bound (x:ℝ) : x*(1-x) ≤ 1/4 :=
  le_div zero_lt_four (numerator_bound x)
