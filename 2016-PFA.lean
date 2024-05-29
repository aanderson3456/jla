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
One could use the p-adic valuation to extend to infinitely many sets.

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
