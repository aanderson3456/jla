import Mathlib.Topology.MetricSpace.PiNat

/-
The paper

Unique paths as formal points
Thierry Coquand, Peter Schuster

mentions WKL₀. Here we state it and prove a converse; this converse does not require the property
of being a tree.

It would not be too hard to prove `wkl` for `Fin 2` using the pigeonhole principle;
instead we refer the reader to
an equivalent result at https://github.com/bjoernkjoshanssen/jla/blob/main/2012-dorais-hirst-shafer.lean

We do prove `wkl` for `Fin 1`, which includes a nice exercise in list induction, `zerolist`.

-/

def tree {α : Type} (T : Set (List α)) : Prop :=
  ∀ σ ∈ T, ∀ τ, τ <+: σ → τ ∈ T

def infi {α : Type} (T : Set (List α)) : Prop :=
  ∀ n : ℕ, ∃ σ ∈ T, σ.length ≥ n

def has_a_path {α : Type} (T : Set (List α)) : Prop :=
  ∃ p : ℕ → α, ∀ k, List.ofFn (λ i : Fin k ↦ p i.1) ∈ T

lemma easier_than_wkl {α : Type} : ∀ T : Set (List α), has_a_path T → infi T := by
  intro T ⟨p,h⟩ n
  use (List.ofFn fun i : Fin n ↦ p i.1)
  constructor
  . exact h _
  . simp only [List.length_ofFn, ge_iff_le, le_refl]


def wkl {α : Type} [Fintype α] := ∀ T : Set (List α), tree T → infi T → has_a_path T

theorem zerolist : ∀ (σ : List (Fin 1)), σ = List.ofFn (λ i : Fin σ.length ↦ 0)
| [] => by simp
| a :: y => by
  rw [zerolist y]
  simp
  exact Fin.fin_one_eq_zero a

example : @wkl (Fin 1) _ := by
  unfold wkl
  intro T hT hi
  use (λ _ ↦ 0)
  intro k
  obtain ⟨σ,hσ⟩ := hi k
  have : σ = List.ofFn (λ i : Fin σ.length ↦ 0) := zerolist σ
  exact hT σ hσ.1 (List.ofFn (λ _ : Fin k ↦ 0)) (by
    rw [this]
    simp
    unfold List.IsPrefix
    exists List.replicate (σ.length - k) 0
    simp
    have : σ.length = (σ.length - k) + k := by
      ring_nf
      exact (Nat.sub_eq_iff_eq_add hσ.2).mp rfl
    nth_rewrite 2 [this]
    have : ∀ a b : ℕ, List.replicate a (0:Fin 1)  ++ List.replicate b 0 = List.replicate (a+b) 0 := by
      intro a b
      exact (List.replicate_add a b 0).symm
    have U := this k (σ.length - k)
    rw [add_comm]
    tauto
  )
