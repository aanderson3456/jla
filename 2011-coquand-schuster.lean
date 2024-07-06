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

To prove that `WKL` does not hold for `ℕ`, which is true since ℕ^ℕ is not compact, we need another
infiniteness of trees that does not use length.

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

/-- This definition only makes sense for finite α. -/
def wkl {α : Type} [Fintype α] := ∀ T : Set (List α), tree T → infi T → has_a_path T

/-- This definition makes sense in general. -/
def WKL {α : Type} := ∀ T : Set (List α), tree T → Infinite T → has_a_path T

example : ¬ @WKL ℕ := by
  unfold WKL
  push_neg
  use (λ σ ↦ σ.length ≤ 1)
  constructor
  unfold tree
  intro σ hσ
  intro τ hτ
  obtain ⟨u,hu⟩ := hτ
  aesop
  have : (τ ++ u).length ≤ 1 := hσ
  show τ.length ≤ 1
  calc
    τ.length ≤ (τ ++ u).length := by apply List.IsPrefix.length_le;simp
    _        ≤ _ := by exact hσ

  constructor
  exact @Infinite.of_surjective ({σ : List ℕ // σ.length ≤ 1}) ℕ _
    (λ σ ↦ dite (σ.1.length = 0) (λ _ ↦ 0) (λ h ↦ σ.1.get ⟨0,Nat.zero_lt_of_ne_zero h⟩
    )) (by intro n; use ⟨[n],by simp⟩; simp)
  unfold has_a_path
  push_neg
  intro p
  use 2
  show ¬ [p 0,p 1].length ≤ 1
  simp

theorem zerolist : ∀ (σ : List (Fin 1)), σ = List.ofFn (λ i : Fin σ.length ↦ 0)
| [] => by simp
| a :: y => by
  rw [zerolist y]
  simp only [Fin.isValue, List.ofFn_const, List.length_cons, List.length_replicate,
    Nat.succ_eq_add_one, List.ofFn_succ, List.cons.injEq, and_true]
  exact Fin.fin_one_eq_zero a

example : @wkl (Fin 1) _ := by
  intro T hT hi
  use (λ _ ↦ 0)
  intro k
  obtain ⟨σ,hσ⟩ := hi k
  exact hT σ hσ.1 (List.ofFn (λ _ : Fin k ↦ 0)) (by
    rw [zerolist σ]
    simp only [Fin.isValue, List.ofFn_const]
    exists List.replicate (σ.length - k) 0
    nth_rewrite 2 [(Nat.sub_eq_iff_eq_add hσ.2).mp rfl]
    rw [← List.replicate_add, add_comm]
  )
