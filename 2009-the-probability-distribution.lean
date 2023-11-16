import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-
Formal verification of
"The probability distribution as a computational resource for randomness testing"
https://arxiv.org/pdf/1408.2850.pdf
Page 5
3rd displayed equation
Second "equals" sign
-/

theorem page5_display3_equals2 (b:ℝ): 2^(b+1) * 4^(b-1) = 2^(3*b-1):=
  (calc
  2^(3*b-1) = 2^(b+1 + 2*(b-1))     := by ring_nf
  _         = 2^(b+1) * 2^(2*(b-1)) := Real.rpow_add zero_lt_two _ _
  _         = 2^(b+1) * (2^2)^(b-1) := by rw [Real.rpow_mul zero_le_two _ _]
  _         = 2^(b+1) * 4^(b-1)     := by norm_num).symm
