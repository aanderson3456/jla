import Mathlib.RingTheory.Int.Basic
import Mathlib.Algebra.BigOperators.Basic
/- We prove some special cases of Dickson's Conjecture as stated in
`On factoring of unlimited integers` by KAREL HRBACEK:
 the case where each aᵢ=0, and the case where each gcd(aᵢ,bᵢ)>1.

Dickson's Conjecture is trivial for ℓ = 0
and we do not need Hrbacek's assumption that ℓ ≥ 1.
 -/

open Finset
def prod_f {ℓ : ℕ} (a b : Fin ℓ → ℕ) : ℕ → ℕ :=
  λ k ↦ Finset.prod univ (λ i : Fin ℓ ↦ a i + b i * k)

theorem dickson_gcd {ℓ : ℕ} (a b: Fin ℓ → ℕ)
  (ha : ∀ i, Nat.gcd (a i) (b i) > 1)
  (hc : ¬ (∃ n, n > 1 ∧ ∀ k, n ∣ (prod_f a b k))) (i : Fin ℓ) (n₀:ℕ) :
  ∃ n ≥ n₀, (a i + b i * n).Prime := by
  by_cases h : ∀ i, b i = 1
  . rw [h i]
    simp
    exfalso
    let h₀ := ha i
    let h₁ := h i
    rw [h₁] at h₀
    simp at h₀
  . simp at h
    obtain ⟨i,_⟩ := h
    exfalso
    contrapose hc
    simp
    exists Nat.gcd (a i) (b i)
    constructor
    . exact ha i
    . intro k
      let h₀ := prod_dvd_prod_of_subset {i} univ
        (λ j : Fin ℓ ↦ a j + b j * k) (subset_univ {i})
      rw [prod_singleton] at h₀
      unfold prod_f
      have h₁ : b i ∣ b i * k := Nat.dvd_mul_right (b i) k
      have h₂: (a i).gcd (b i) ∣ a i := Nat.gcd_dvd_left (a i) (b i)
      have h₃: (a i).gcd (b i) ∣ b i := Nat.gcd_dvd_right (a i) (b i)
      have h₄: (a i).gcd (b i) ∣ a i + b i * k := by
        refine (Nat.dvd_add_iff_right h₂).mp ?_
        exact Nat.dvd_trans h₃ h₁
      exact Nat.dvd_trans h₄ h₀


/-- This one is strange since `a i` does not appear in the conclusion: -/
lemma aux {ℓ : ℕ} (a b: Fin ℓ → ℕ) (hb : ∀ i, b i ≥ 1)
  (ha : ∀ i, b i ∣ a i)
  (hc : ¬ (∃ n, n > 1 ∧ ∀ k, n ∣ (prod_f a b k))) (i : Fin ℓ) (n₀:ℕ) :
  ∃ n ≥ n₀, (b i * n).Prime := by
  by_cases h : ∀ i, b i = 1
  . rw [h i]
    simp
    exact Nat.exists_infinite_primes n₀
  . simp at h
    obtain ⟨i,hi⟩ := h
    exfalso
    contrapose hc
    simp
    exists b i
    constructor
    . exact Nat.lt_of_le_of_ne (hb i) fun a ↦ hi (id (Eq.symm a))
    . intro k
      let h₀ := prod_dvd_prod_of_subset {i} univ
        (λ j : Fin ℓ ↦ a j + b j * k) (subset_univ {i})
      rw [prod_singleton] at h₀
      unfold prod_f
      have h₁ : b i ∣ b i * k := Nat.dvd_mul_right (b i) k
      have h₂ : b i ∣ a i + b i * k := (Nat.dvd_add_iff_right (ha i)).mp h₁
      simp at h₀
      exact Nat.dvd_trans h₂ h₀


  theorem dickson_linear {ℓ : ℕ} {a b: Fin ℓ → ℕ} {hb : ∀ i, b i ≥ 1}
  (ha : ∀ i, a i = 0)
  (hc : ¬ (∃ n, n > 1 ∧ ∀ k, n ∣ (prod_f a b k))) (i : Fin ℓ) (n₀:ℕ) :
  ∃ n ≥ n₀, (a i + b i * n).Prime := by
    rw [ha i]
    simp
    exact aux a b hb (by intro i;rw [ha i];simp) hc i n₀
