import Mathlib.Topology.MetricSpace.PiNat

 /-

In the paper

A constructive proof of Simpson’s Rule
THIERRY COQUAND
BAS SPITTERS

uniform continuity is discussed. We define it in a concrete setting here, and prove that y=x^2 is not uniformly continuous.

Authors: Bjørn Kjos-Hanssen, Clark Eggerman
-/


def is_uniformly_continuous (f : ℝ → ℝ) : Prop := ∀ ε : ℝ, ε > 0 → ∃ δ : ℝ, δ > 0 ∧ ∀ x y : ℝ, |x - y| < δ → |(f x) - (f y)| < ε

example : ¬ is_uniformly_continuous (λ x ↦ x^2) := by
  intro hc
  unfold is_uniformly_continuous at hc
  contrapose hc
  push_neg
  use 1
  constructor
  . exact Real.zero_lt_one
  . intro δ hδ
    use 1/δ
    use (1/δ + δ/2)
    constructor
    . ring_nf
      have h₁ : |-(δ/2)| = δ/2 := by
        simp
        linarith
      ring_nf at h₁
      rw [h₁]
      have h₀: δ/2 < δ := by exact div_two_lt_of_pos hδ
      ring_nf at h₀
      exact h₀
    . simp

      ring_nf
      have : δ * δ⁻¹ = 1 := by
        refine CommGroupWithZero.mul_inv_cancel δ ?_
        exact Ne.symm (ne_of_lt hδ)
      rw [this]
      simp
      ring_nf
      have : -1 + δ ^ 2 * (-1 / 4) = - (1 + (δ/2)^2) := by ring_nf
      rw [this]
      have h₄ : 0 ≤ (δ/2)^2 := sq_nonneg (δ / 2)
      have : |(-(1 + (δ/2) ^ 2))| = ((1 + (δ/2)^2)) := by
        rw [abs_neg]
        rw [abs_eq_self]
        linarith
      rw [this]
      suffices 1 + 0 ≤ 1 + (δ / 2) ^ 2 by
        simp at this;simp;tauto

      exact (add_le_add_iff_left 1).mpr h₄
