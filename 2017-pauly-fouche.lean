import Mathlib.MeasureTheory.Constructions.Prod.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Topology.MetricSpace.Baire
import Mathlib.Init.Order.Defs
import Mathlib.Topology.Clopen
import Init.Prelude
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-

In Pauly and Fouche's paper "How constructive is constructing measures?"
in the proof of Example 15 they write:
`let d be the restriction of the usual metric on Cantor space.`

Here we construct what we think they meant by `the usual metric on Cantor space`,
except that we use e^n instead of 2^n.

-/


theorem differ {A B : ℕ → Bool} (h : A ≠ B) :  ∃ x, A x ≠ B x := by exact Function.ne_iff.mp h
def getval {A B : ℕ → Bool} (h : A ≠ B) : ℕ := Nat.find (differ h)

def getval' {A B : ℕ → Bool} (h : A ≠ B) : ℝ := getval h

open Classical

noncomputable instance  :
  MetricSpace (ℕ → Bool) := {
    dist := λ A B ↦ dite (A=B) (λ h ↦ 0) (λ h ↦ Real.exp (- (getval' h)))
    dist_self := by intro A;simp
    dist_comm := by
      intro A B
      unfold dist
      simp
      by_cases h : A = B
      . rw [dif_pos h]
        rw [dif_pos h.symm]
      . rw [dif_neg h]
        have : ¬ B = A := by exact Ne.symm h
        rw [dif_neg this]
        have : getval' h = getval' this := by
          unfold getval' getval
          simp;congr;ext;tauto
        rw [this]
    dist_triangle := by
      intro A B C
      unfold dist
      simp
      by_cases hac : A = C
      . subst hac
        simp
        by_cases g : A = B
        . subst g
          simp
        . rw [dif_neg g]
          have : ¬ B = A := by
            exact Ne.symm g
          rw [dif_neg this]
          apply add_nonneg
          exact Real.exp_nonneg (-getval' g)
          exact Real.exp_nonneg (-getval' this)
      . rw [dif_neg hac]
        by_cases hab : A = B
        . subst hab
          simp
          rw [dif_neg hac]
        . rw [dif_neg hab]
          by_cases hbc : B = C
          subst hbc
          simp
          rw [dif_neg hbc]
          -- the only interesting case is this:
          have h₀: max (Real.exp (-getval' hab)) (Real.exp (-getval' hbc)) ≤
            (Real.exp (-getval' hab))
            +
            (Real.exp (-getval' hbc)) := by
              apply max_le
              . have : (0:ℝ) ≤ Real.exp (-getval' hbc) := by
                  exact Real.exp_nonneg (-getval' hbc)
                exact le_add_of_nonneg_right this
              . have : (0:ℝ) ≤ Real.exp (-getval' hab) := by
                  exact Real.exp_nonneg (-getval' hab)
                exact le_add_of_nonneg_left this
          suffices Real.exp (-getval' hac) ≤ max (Real.exp (-getval' hab)) (Real.exp (-getval' hbc)) by
            exact le_trans this h₀
          -- and here is the only truly interesting part:
          unfold getval' getval
          have h₁: ∀ x, A x ≠ C x → A x ≠ B x ∨ B x ≠ C x := by
            intro x H;by_contra H₀
            simp at H₀
            have : A x = B x ∧ B x = C x := by exact and_iff_not_or_not.mpr H₀
            apply H
            apply Eq.trans
            exact this.1
            exact this.2
          have : A (getval hac) ≠ C (getval hac) := by
            unfold getval
            exact Nat.find_spec (differ hac)
          let xac := getval hac
          have hxac: A xac ≠ B xac ∨ B xac ≠ C xac := by
            exact h₁ xac this
          have : min (Nat.find (differ hab)) (Nat.find (differ hbc)) ≤ Nat.find (differ hac) := by
            apply min_le_iff.mpr
            cases hxac with
            |inl hab => left;apply Nat.find_le;exact hab
            |inr hbc => right;apply Nat.find_le;exact hbc
          have fact₀ (u v : ℝ) : max (Real.exp u) (Real.exp v) = Real.exp (max u v) := by
            let Q := @Monotone.map_max ℝ ℝ _ _ (λ x ↦ Real.exp x) u v (by
              apply Real.exp_monotone
            )
            simp at Q
            rw [Q]
          rw [fact₀]
          apply Real.exp_monotone
          simp
          cases hxac with
          |inl hl =>
            left;intro m hm;
            by_contra hc
            let Q := @Nat.find_le m (λ n ↦ A n ≠ C n) _ (differ hac) hc
            have : xac = Nat.find (_ : ∃ x, A x ≠ C x) := rfl
            rw [← this] at Q
            let R := hm xac Q
            tauto
          |inr hr =>
            right;intro m hm;
            by_contra hc
            let Q := @Nat.find_le m (λ n ↦ A n ≠ C n) _ (differ hac) hc
            have : xac = Nat.find (_ : ∃ x, A x ≠ C x) := rfl
            rw [← this] at Q
            let R := hm xac Q
            tauto

    edist_dist := (λ x y ↦ by exact (ENNReal.ofReal_eq_coe_nnreal _).symm)
    eq_of_dist_eq_zero := by
      intro A B h;
      have : dite (A=B) (λ h ↦ 0) (λ h ↦ Real.exp (- (getval' h))) = 0 := h
      by_contra h₀
      rw [dif_neg h₀] at this
      contrapose this
      exact Real.exp_ne_zero (-getval' h₀)
  }
