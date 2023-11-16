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
