import Mathlib.Topology.Defs.Basic
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.Topology.Defs.Basic
/-

The paper

Preface to the special issue for
The Fifth Workshop on Formal Topology
THIERRY COQUAND
MARIA EMILIA MAIETTI
ERIK PALMGREN

introduces Formal Topology, which is a constructive approach to pointfree topology.
Here we instead look at topologies *with points*, over finite sets and show:
 - there is a unique topology on `Fin 0`;
 - there is a unique topology on `Fin 1`;
 - there exist two distinct topologies on `Fin 2`
 - We also construct the remaining two topologies on `Fin 2` giving a total of 4.


-/

-- There is only one topology on `Fin 0`:
example ( σ τ : TopologicalSpace (Fin 0)) : σ.IsOpen = τ.IsOpen := by
  apply funext
  intro S
  have : S = ∅ := by
    ext s
    constructor
    . intro
      have Q := s.2
      simp at Q
    . intro h;simp at h
  subst this
  apply propext
  constructor
  . intro; exact @isOpen_empty _ τ
  . intro; exact @isOpen_empty _ σ

-- There is only one topology on `Fin 1`:
example ( σ τ : TopologicalSpace (Fin 1)) : σ.IsOpen = τ.IsOpen := by
  apply funext
  intro S
  by_cases H : S = ∅
  . subst H
    have h₀ := @isOpen_empty _ σ
    have h₁ := @isOpen_empty _ τ
    apply propext
    tauto
  . have : S = Set.univ := by
      ext s
      constructor
      . intro; trivial
      . intro
        have : s = 0 := by exact Fin.fin_one_eq_zero s
        subst this
        have : ∃ a, a ∈ S := by
          refine Set.nonempty_def.mp ?_
          exact Set.nonempty_iff_ne_empty.mpr H
        obtain ⟨a,ha⟩ := this
        have : a = 0 := by exact Fin.fin_one_eq_zero a
        subst this
        tauto
    subst this
    have : σ.IsOpen Set.univ := @TopologicalSpace.isOpen_univ _ σ
    have : τ.IsOpen Set.univ := @TopologicalSpace.isOpen_univ _ τ
    apply propext
    tauto


-- There are two distinct topologies on `Fin 2`:
example : ∃ ( σ τ : TopologicalSpace (Fin 2)), σ.IsOpen ≠ τ.IsOpen := by
  use ⊥ -- discrete topology
  use ⊤ -- trivial topology
  intro hc
  have h₀: (⊥ : TopologicalSpace (Fin 2)).IsOpen {0} := trivial

  have : ¬@IsOpen (Fin 2) ⊤ {0} := by
    rw [TopologicalSpace.isOpen_top_iff]
    simp only [Set.singleton_ne_empty, false_or]
    intro h
    cases h.ge (Set.mem_univ 1)

  have h₁: ¬ (⊤ : TopologicalSpace (Fin 2)).IsOpen {0} := by
    change ¬@IsOpen (Fin 2) ⊤ {0} -- thanks to Eric Wieser for this line
    intro hc
    aesop
  aesop

-- Here are two more topologies on `Fin 2`.
-- In fact a topology on `Fin 2` must contain `Set.univ` and `∅`,
-- and then there are four possibilities depending on which of `{0}`, `{1}` are included.
def mytop (z : Fin 2): TopologicalSpace (Fin 2) :=
{
  IsOpen := λ S ↦ S = ∅ ∨ S = Set.univ ∨ S = {z}
  isOpen_univ := by tauto
  isOpen_inter := by
    intro S T hS hT
    cases hS with
    |inl h => subst h;left;simp
    |inr h =>
      cases h with
      |inl h => subst h; cases hT with
        |inl h => subst h;simp
        |inr h => cases h with
          |inl h => subst h;simp
          |inr h => subst h;simp
      |inr h => subst h;cases hT with
        |inl h => subst h;simp
        |inr h => cases h with
          |inl h => subst h;simp
          |inr h => subst h;simp
  isOpen_sUnion := by
    intro S hS
    simp at hS
    by_cases H₀ : Set.univ ∈ S
    . right;left;refine Set.sUnion_eq_univ_iff.mpr ?_;
      intro a;exists Set.univ
    . by_cases H₁ : {z} ∈ S
      . right;right;ext i;simp;
        constructor
        intro h;
        obtain ⟨t,ht⟩ := h
        let Q := hS t ht.1
        cases Q with
          |inl h => subst h;simp at ht
          |inr h => cases h with
            |inl h => subst h;tauto
            |inr h => subst h;tauto
        intro h
        subst h
        exists {i}
      . left;ext i;simp;intro s hs;
        let Q := hS s hs
        cases Q with
        |inl h => subst h;simp
        |inr h => cases h with
          |inl h => subst h;simp;tauto
          |inr h => subst h;simp;tauto
}
