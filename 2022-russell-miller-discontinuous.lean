-- import Mathlib.Algebra.IndicatorFunction
import Mathlib.MeasureTheory.Constructions.Prod.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Topology.MetricSpace.Baire
import Mathlib.Init.Order.Defs
import Mathlib.Topology.Clopen
import Init.Prelude
import Mathlib.Dynamics.Ergodic.MeasurePreserving

/-
Russell Miller's 2022 paper Effectivizing Luzin's Theorem discusses
approximation of discontinuous functions on ℝ by continuous ones.

Here we merely demonstrate that there exists a discontinous function on the Cantor space.
(In fact, the example we give is equal to a continuous function on a set of full measure
for any non-atomic measure, although we don't prove that.)
-/

instance : BaireSpace (ℕ → Bool) := BaireSpace.of_t2Space_locallyCompactSpace

open Set

open Classical


/-- Definition 13 in `A tractable case`. Apr 11, 2024.-/
def searrow {α : Type} (σ : Σ n : ℕ, Fin n → α) (X : ℕ → α) : ℕ → α := by
  intro n
  by_cases h : (n < σ.1)
  exact σ.2 ⟨n,h⟩
  exact X n

infix:50 " ↘ " => searrow

/-- It is not clear what we gain by insisting that I is an initial segment of ℕ. -/
def condition {α : Type} := Σ I : Finset ℕ, I → Set α

def extendedBy {α : Type} (σ τ : @condition α)
 : Prop :=
  ∃ (h : σ.1 ⊆ τ.1), ∀ i (g : i ∈ σ.1), τ.2 ⟨i,by tauto⟩ ⊆ σ.2 ⟨i,g⟩

infix:50 " ≼ " => extendedBy


def extendedByℕ {α : Type}  (σ : @condition α) (X : ℕ → α)
 : Prop :=
  ∀ i (g : i ∈ σ.1), X i ∈ σ.2 ⟨i,g⟩

infix:50 " ≼ " => extendedByℕ

theorem extendedBy_transitiveℕ {α : Type} {u v : @condition α}
  {X : ℕ → α} (h₀ : u ≼ v) (h₁ : v ≼ X): u ≼ X := by
    unfold extendedByℕ at *
    unfold extendedBy at h₀
    intro j hj
    obtain ⟨h,h₂⟩ := h₀
    let Q₁ := h₁ j (h hj)
    let Q₂ := h₂ j hj Q₁
    exact Q₂


theorem open_point {α : Type} [TopologicalSpace α] [DiscreteTopology α] (n:ℕ) (b:α)
:
IsOpen {A : ℕ → α | A n = b} := by
  refine isOpen_pi_iff.mpr ?_
  intro A hA
  exists {n}
  exists (λ _ ↦ {b})
  constructor
  intro z hz
  simp only [Finset.mem_singleton] at hz
  subst hz
  constructor
  exact isOpen_discrete _
  simp only [mem_singleton_iff]
  exact hA
  intro X hX
  show X n = b
  simp only [Finset.coe_singleton, singleton_pi, mem_preimage, Function.eval,
    mem_singleton_iff] at hX
  tauto

lemma open_value {α : Type} [TopologicalSpace α] [DiscreteTopology α]
  (n:ℕ) (b:α) {F : (ℕ → α) → (ℕ → α)} (h : Continuous F) : IsOpen { A | F A n = b}
  := by
  let Q := h.1 { A : ℕ → α | A n = b} (open_point _ _)
  tauto

theorem my_isCompact_iff_finite_subcover₀  {α : Type} [TopologicalSpace α] [DiscreteTopology α]
(F : (ℕ → α) → (ℕ → α)) (n:ℕ)
 {s : Set (ℕ → α)} :
IsCompact s → ∀ (U : { τ : condition // ∀ Y₁ Y₂ : (ℕ → α), τ ≼ Y₁ → τ ≼ Y₂ → F Y₁ n = F Y₂ n} → Set (ℕ → α)),
(∀ (i : { τ : condition // ∀ Y₁ Y₂ : (ℕ → α), τ ≼ Y₁ → τ ≼ Y₂ → F Y₁ n = F Y₂ n}), IsOpen (U i))
→ s ⊆ ⋃ (i : { τ : condition // ∀ Y₁ Y₂ : (ℕ → α), τ ≼ Y₁ → τ ≼ Y₂ → F Y₁ n = F Y₂ n}), U i
→ ∃ (t : Finset { τ : condition // ∀ Y₁ Y₂ : (ℕ → α), τ ≼ Y₁ → τ ≼ Y₂ → F Y₁ n = F Y₂ n}), s ⊆ ⋃ i ∈ t, U i
:= by
  let Q := (@isCompact_iff_finite_subcover (ℕ → α))
  intro hs
  apply Q.mp
  exact hs


theorem my_isCompact_iff_finite_subcover₁ {α : Type} [ TopologicalSpace α] [DiscreteTopology α]
  [CompactSpace (ℕ → α)]
  (F : (ℕ → α) → (ℕ → α)) (n:ℕ):
(∀ (σ : { τ : condition // ∀ Y₁ Y₂ : (ℕ → α), τ ≼ Y₁ → τ ≼ Y₂ → F Y₁ n = F Y₂ n}),
 IsOpen ({X : (ℕ → α) | σ ≼ X}))
→ (Set.univ : Set (ℕ → α)) ⊆ ⋃ (σ : { τ : condition // ∀ Y₁ Y₂ : (ℕ → α), τ ≼ Y₁ → τ ≼ Y₂ → F Y₁ n = F Y₂ n}),
{X : (ℕ → α) | σ ≼ X}
  → ∃ (t : Finset { τ : condition // ∀ Y₁ Y₂ : (ℕ → α), τ ≼ Y₁ → τ ≼ Y₂ → F Y₁ n = F Y₂ n}), (Set.univ : Set (ℕ → α))
  ⊆ ⋃ σ ∈ t, {X : (ℕ → α) | σ ≼ X}
:= by
    exact my_isCompact_iff_finite_subcover₀ F n isCompact_univ (λ σ ↦ {X : (ℕ → α) | σ ≼ X})


lemma cones_are_open  {α : Type} [TopologicalSpace α] [DiscreteTopology α]
  (σ : @condition α) : IsOpen {X : ℕ → α | σ ≼ X} := by
      apply isOpen_pi_iff.mpr
      intro Y hY
      exists σ.1
      exists (λ i : ℕ ↦ by
        by_cases H : i ∈ σ.1.1
        exact σ.2 ⟨i,H⟩
        exact Set.univ
      )
      constructor
      . intro i hi
        constructor
        . simp
        . simp only [Finset.mem_val]
          rw [dif_pos hi]
          simp only [mem_setOf_eq] at hY
          exact hY i hi

      . simp only [Finset.mem_val]
        intro Z hZ i hi
        let Q := hZ i hi
        simp only [mem_pi, Finset.mem_coe] at Q
        rw [dif_pos hi] at Q
        exact Q

/-- This is the too-obvious version of the use principle, before using compactness
as in isCompact_iff_finite_subcover. -/
theorem prep_for_compactness_and_use₀ {α : Type} [TopologicalSpace α] [DiscreteTopology α] (F : (ℕ → α) → (ℕ → α))
  (hF : Continuous F) (n:ℕ) (X : (ℕ → α)) :
  ∃ σ : condition, σ ≼ X ∧ ∀ Y : (ℕ → α), σ ≼ Y → F Y n = F X n := by
    obtain ⟨I,hI⟩ := isOpen_pi_iff.mp (open_value n (F X n) hF) X rfl
    obtain ⟨U,hU⟩ := hI
    let τ : condition := ⟨I,λ n ↦ U n.1⟩
    exists τ
    constructor
    . intro i hi
      exact (hU.1 i hi).2
    . intro Y hY
      apply hU.2
      exact hY

/-- This version makes it clear that the set of X for which σ exists is open: -/
theorem prep_for_compactness_and_use₁ {α : Type} [TopologicalSpace α] [DiscreteTopology α] (F : (ℕ → α) → (ℕ → α))
  (hF : Continuous F) (n:ℕ) (X : (ℕ → α)) :
  ∃ σ : condition, (∀ Y₁ Y₂ : (ℕ → α), σ ≼ Y₁ → σ ≼ Y₂ → F Y₁ n = F Y₂ n) ∧ σ ≼ X := by
  obtain ⟨σ,hσ⟩ := prep_for_compactness_and_use₀ F hF n X
  exists σ
  constructor
  . intro Y₁ Y₂ hY₁ hY₂
    calc F Y₁ n = F X  n :=  hσ.2 Y₁ hY₁
    _           = F Y₂ n := (hσ.2 Y₂ hY₂).symm
  . tauto


/-- Apr 14, 2024-/
theorem bounded_use_principle₀ {α : Type} [TopologicalSpace α] [DiscreteTopology α]
[CompactSpace (ℕ → α)] (F : (ℕ → α) → (ℕ → α)) (hF : Continuous F) (n:ℕ):
∃ (t : Finset { τ : condition // ∀ Y₁ Y₂ : (ℕ → α), τ ≼ Y₁ → τ ≼ Y₂ → F Y₁ n = F Y₂ n}), (Set.univ : Set (ℕ → α))
  ⊆ ⋃ σ ∈ t, {X : (ℕ → α) | σ ≼ X}
:= by
    have : (Set.univ : Set (ℕ → α)) ⊆
      ⋃ (σ : { τ : condition // ∀ Y₁ Y₂ : (ℕ → α), τ ≼ Y₁ → τ ≼ Y₂ → F Y₁ n = F Y₂ n}), {Y : (ℕ → α) | σ ≼ Y} := by
        intro Y
        intro
        simp
        exact prep_for_compactness_and_use₁ F hF n Y
    exact my_isCompact_iff_finite_subcover₁ _ _ (λ σ ↦ cones_are_open σ.1) this



def condition_of_fin {α : Type}  (σ : (Σ n, Fin n → α)) : @condition α
  := ⟨(Finset.range σ.1), λ i ↦ {σ.2 ⟨i.1, List.mem_range.mp i.2⟩}⟩

lemma sea_extends {α : Type} (σ : Σ n, Fin n → α) (X : ℕ → α) : (@condition_of_fin α σ) ≼ (σ ↘ X)
  := by
    intro j hj
    unfold condition_of_fin searrow
    simp
    rw [dif_pos _]



lemma condition_extended_by_of_fin
{α : Type}
{τ : @condition α}
{σ : (k : ℕ) × (Fin k → α)}
(hN : τ.fst.Nonempty)
(h : Finset.max' τ.fst hN < σ.fst)
: τ.fst ⊆ (condition_of_fin σ).fst
:= by
    intro i hi
    unfold condition_of_fin
    simp only [Finset.mem_range]
    suffices i ≤ Finset.max' τ.fst hN by
      calc
      _ ≤ Finset.max' τ.1 hN := this
      _ < _ := h
    apply Finset.le_max'
    exact hi

/-- Completed Apr 15, 2024.-/
theorem condition_of_max {α : Type} (τ : condition) (X : (ℕ → α))
(σ : Σ k, Fin k → α)
(hN : Finset.Nonempty τ.fst)
(h : Finset.max' τ.1 hN < σ.1)
(hτ : τ ≼ (σ ↘ X)) : τ ≼ condition_of_fin σ := by

  unfold extendedByℕ at hτ
  unfold extendedBy
  exists condition_extended_by_of_fin hN h
  intro i hi
  intro b hb
  let Q := hτ i hi
  simp at Q
  unfold condition_of_fin at hb
  simp at hb
  subst hb
  unfold searrow at Q
  have : i < σ.1 := by
    suffices i ≤ Finset.max' τ.fst hN by
      calc
      _ ≤ Finset.max' τ.1 hN := this
      _ < _ := h
    apply Finset.le_max'
    exact hi
  rw [dif_pos this] at Q
  exact Q


theorem emp_extendedBy {α : Type} {σ : @condition α} (he : σ.1 = ∅) (X : (ℕ → α)) :
σ ≼ X := by
  unfold extendedByℕ
  intro i hi
  rw [he] at hi
  contrapose hi
  simp


theorem bounded_use_principle₁ {α : Type} [TopologicalSpace α] [DiscreteTopology α]
[CompactSpace (ℕ → α)] (F : (ℕ → α) → (ℕ → α)) (hF : Continuous F) (n:ℕ):
∃ u : ℕ, ∀ σ : Σ k, Fin k → α, σ.1 = u →
  ∀ X Y : ℕ → α, F (σ ↘ X) n = F (σ ↘ Y) n := by

    obtain : Trans (@extendedBy α) extendedByℕ extendedByℕ := {
      trans := λ h₀ h₁ ↦ extendedBy_transitiveℕ h₀ h₁
    }


    obtain ⟨t,ht⟩ := bounded_use_principle₀ F hF n
    let I := Finset.biUnion t (λ σ ↦ σ.1.1)
    by_cases hN : Finset.Nonempty I
    . let u := Finset.max' I hN
      exists u.succ
      intro σ hσu X Y
      suffices ∃ τ ∈ t, τ ≼ (σ ↘ X) ∧ τ ≼ (σ ↘ Y) by
        obtain ⟨τ,hτ⟩ := this
        exact τ.2 (σ ↘ X) (σ ↘ Y) hτ.2.1 hτ.2.2
      let Q := ht (show (σ ↘ X) ∈ Set.univ by trivial)
      simp at Q
      obtain ⟨τ₀,hτ₀⟩ := Q
      let hτt := hτ₀.1.2
      let ⟨τ₁,hτ₁⟩ := hτ₀

      exists ⟨τ₀,τ₁.1⟩
      constructor
      . exact hτt
      . constructor
        . exact hτ₁

        . simp
          by_cases H : Finset.Nonempty τ₀.fst
          . -- yes
            have : Finset.max' τ₀.fst H < σ.fst := by
              rw [hσu]
              suffices Finset.max' τ₀.1 H ≤ u by
                exact Nat.lt_succ.mpr this
              rw [Finset.max'_le_iff]
              intro i hi
              apply Finset.le_max'
              simp
              exists τ₀
            calc
            τ₀ ≼ condition_of_fin σ := condition_of_max τ₀ X σ H this hτ₁
            _  ≼ (σ ↘ Y)            := sea_extends _ _
          . -- no
            simp at H
            exact emp_extendedBy H _
    . -- since the biUnion is empty, the empty condition must force it
      exists 0
      intro σ; intro; intro X Y
      let hX := ht (show X ∈ Set.univ from trivial)
      simp at hX hN
      obtain ⟨σX, hσX⟩ := hX
      let emp_σX := hN σX hσX.1.1 hσX.1.2
      exact hσX.1.1 (σ ↘ X) (σ ↘ Y) (emp_extendedBy emp_σX _) (emp_extendedBy emp_σX _)


noncomputable def disco := (
  λ A : ℕ → Bool ↦ ite
    (A = (λ n ↦ false))
    (λ n : ℕ ↦ true)
    (λ n ↦ false)
)

example : ¬ Continuous disco := by
  intro hc
  obtain ⟨u,hu⟩ := @bounded_use_principle₁ Bool _ _ _ disco hc 0
  let Q := hu ⟨u,λ i ↦ false⟩ (by simp) (λ n ↦ false) (λ n ↦ ite (u < n) true false)
  simp at Q
  unfold searrow at Q
  simp at Q
  have : disco (fun n => false) 0 = true := by
    unfold disco
    simp
  rw [this] at Q
  have : disco (fun n => if n < u then false else if u < n then true else false) 0 = false := by
    unfold disco
    have : ¬ (fun n => if n < u then false else if u < n then true else false) = fun n => false
      := by
        intro hc
        have : (fun n => if n < u then false else if u < n then true else false) u.succ
          = (fun n => false) u.succ := by
            rw [hc]
        simp at this
        contrapose this
        simp
        exact Nat.le_succ u
    rw [if_neg this]
  rw [this] at Q
  contrapose Q
  simp
