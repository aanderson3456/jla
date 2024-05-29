import Mathlib.Topology.Clopen
import Mathlib.Data.Nat.Prime
import Mathlib.NumberTheory.SmoothNumbers
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Reflection
import Mathlib.Tactic.NormNum.Prime
import Mathlib.LinearAlgebra.Matrix.ZPow
import Mathlib.Data.Fin.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.LinearAlgebra.Matrix.PosDef


/-

Section 2 of Alan Dow's paper `PFA and complemented subspaces of ℓ_∞/c₀`,
Journal of Logic and Analysis, 2016,
starts: `Let A_n, n ∈ ℕ be a partition of ℕ into infinite sets.`
Here we prove formally that there exists a partition of ℕ into two infinite sets.
One could use the 2-adic valuation to extend to infinitely many sets;
we prove that each such set Aₙ is infinite.

-/
def E : Set Nat := λ k ↦ Even k
def O : Set Nat := λ k ↦ Odd k

example : Infinite E := by
  refine Set.infinite_coe_iff.mpr ?_
  refine Set.infinite_of_forall_exists_gt ?h
  intro a
  exists 2*a.succ
  constructor
  . exists a.succ
    linarith
  . linarith

example : Infinite O := by
  refine Set.infinite_coe_iff.mpr ?_
  refine Set.infinite_of_forall_exists_gt ?h
  intro a
  exists (2*a).succ
  constructor
  . exists a
  . linarith

example : Disjoint E O := by
  unfold E
  unfold O
  refine Set.disjoint_iff_forall_ne.mpr ?_
  intro a ha b hb
  have : ¬ Odd a := by exact Nat.even_iff_not_odd.mp ha
  exact Ne.symm (ne_of_mem_of_not_mem hb this)

example : E ∪ O = Set.univ := by
  unfold E O
  simp
  apply Set.ext
  intro x
  simp
  tauto

def A : ℕ → Set ℕ := λ n ↦ λ k ↦ padicValNat 2 k = n

example {n:ℕ} : Infinite (A n) := by
  refine Set.infinite_coe_iff.mpr ?_
  refine Set.infinite_of_forall_exists_gt ?h
  intro a
  exists 2^n*(2*a+1)
  constructor
  . unfold A padicValNat
    have : 0 < 2^n*(2*a+1) := by
      exact Fin.size_pos'
    simp
    refine Set.mem_def.mpr ?h.left.a
    rw [dif_pos this]
    refine (multiplicity.unique' ?h.left.a.hk ?h.left.a.hsucc).symm
    exact Nat.dvd_mul_right (2 ^ n) (2 * a + 1)
    intro hc
    obtain ⟨b,hb⟩ := hc
    contrapose hb
    suffices ¬2 ^ n * (2 * a + 1) = 2 ^ n  * (2 * b) by
      rw [Nat.pow_succ,Nat.mul_assoc]
      tauto
    simp
    have h₀: Even (2*b) := by exact even_two_mul b
    have h₁: Odd (2*a+1) := by exact odd_two_mul_add_one a
    have h₂ : ¬ Even (2*a+1) := by exact Nat.odd_iff_not_even.mp h₁
    intro hc
    rw [← hc] at h₀
    tauto
  . show a < 2 ^ n * (2 * a + 1)
    calc
    a < 2*a+1 := by
      cases a with
      |zero => simp
      |succ b => linarith
    _ = 1*(2*a+1) := (Nat.one_mul (2 * a + 1)).symm
    _ ≤ 2^n*(2*a+1) := by
      refine Nat.mul_le_mul ?h₁ ?h₂
      exact Nat.one_le_two_pow
      exact Nat.le_refl (2 * a + 1)
