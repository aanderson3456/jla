import Mathlib.LinearAlgebra.Matrix.Trace

/- The first displayed equation in the paper "Covering entropy for types in tracial W^*- algebras" by
DAVID JEKEL includes the term
`τ (X₁ * Y * X₂ * Z) ^ 2`
Here τ is the trace and * is matrix multiplication.
There are two ways to parenthesize this and here we prove their inequivalence.
Perhaps it does not matter for the paper, however.
In that sense, mathematical articles may be underdetermined without being wrong.
-/

def I : Fin 2 → Fin 2 → ℚ := (λ x y ↦ ite (x=y) 1 0) -- = !![ 1,0;0,1]
lemma square : I^2 = I := by unfold I; decide

def τ : (Fin 2 → Fin 2 → ℚ) → ℚ := Matrix.trace
lemma two : τ I = 2 := by unfold τ I Matrix.trace; simp

lemma parentheses_matter : (τ I)^2 ≠ τ (I^2) := by
  rw [square,two];ring_nf;simp

/-- Lean's convention is perhaps surprising here: -/
lemma without_parentheses : τ (I)^2 = (τ I)^2 := rfl
