import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Order.Interval.Set.Basic

/- This concerns the second sentence in the Introduction in the paper
Genericity and UD–random reals by WESLEY CALVERT, JOHANNA N.Y. FRANKLIN.
We define uniform distribution and prove that the constant 0 sequence is not uniformly distributed.
-/

open Finset
def uniformly_distributed (x : ℕ → Set.Ico (0:ℝ) 1) :=
  ∀ a b ε : ℝ, 0 ≤ a → a < b → b ≤ 1 → ε > 0 → ∃ n₀ : ℕ, ∀ n : ℕ, n ≥ n₀ →
    abs (card (filter (λ i : Fin n ↦ a < x i ∧ x i < b) univ) - (b - a) * n) < n * ε

example : ¬ uniformly_distributed (λ n ↦ ⟨0,by simp⟩) := by
  unfold uniformly_distributed
  intro hc
  obtain ⟨n₀,hn₀⟩ := hc (1/2) 1 (1/2) (by
    refine one_div_nonneg.mpr ?_
    exact zero_le_two
  ) (one_half_lt_one) (Preorder.le_refl 1) (one_half_pos)
  let Q := hn₀ n₀ (Nat.le_refl n₀)
  simp at Q
  have : ¬ (2:ℝ) < 0 := by
    refine not_lt.mpr ?_
    exact zero_le_two
  rw [if_neg this] at Q
  simp at Q
  ring_nf at Q
  contrapose Q
  show  ¬|(n₀:ℝ) * (1 / 2)| < (n₀:ℝ) * (1 / 2)
  suffices ¬(n₀:ℝ) * (1 / 2) < (n₀:ℝ) * (1 / 2) by
    contrapose this
    simp
    simp at this
    have h₀: (n₀:ℝ) * (2⁻¹) < (n₀:ℝ) * (2⁻¹) := calc
      (n₀:ℝ) * (2⁻¹) ≤ abs ((n₀:ℝ) * (2⁻¹)) := by exact le_abs_self ((n₀:ℝ) * 2⁻¹)
      _ < _ := this
    exact (lt_self_iff_false ((n₀:ℝ) * (2⁻¹))).mp h₀
  exact gt_irrefl ((n₀:ℝ) * (1 / 2))
