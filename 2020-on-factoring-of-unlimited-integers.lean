import Mathlib.RingTheory.Int.Basic
import Mathlib.Algebra.BigOperators.Basic
/- We prove a special case of Dickson's Conjecture as stated in
`On factoring of unlimited integers` by KAREL HRBACEK:
 the case where each aᵢ=0.

Dickson's Conjecture is trivial for ℓ = 0
and we do not need Hrbacek's assumption that ℓ ≥ 1.
 -/

open Finset
def prod_f {ℓ : ℕ} (b : Fin ℓ → ℕ) : ℕ → ℕ :=
  λ k ↦ Finset.prod univ (λ i : Fin ℓ ↦ b i * k)

theorem dickson_linear {ℓ : ℕ} {b: Fin ℓ → ℕ} {hb : ∀ i, b i ≥ 1}
  (hc : ¬ (∃ n, n > 1 ∧ ∀ k, n ∣ (prod_f b k))) (i : Fin ℓ) (n₀:ℕ) :
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
      let Q := prod_dvd_prod_of_subset {i} univ
        (λ j : Fin ℓ ↦ b j * k) (subset_univ {i})
      rw [prod_singleton] at Q
      exact Nat.dvd_trans (Nat.dvd_mul_right (b i) k) Q
