import Mathlib.RingTheory.Int.Basic

/- We prove a special case of
Dickson's Conjecture as stated in
`On factoring of unlimited integers`
by KAREL HRBACEK:
ℓ = 1, a₁ = 0.
-/
def f {b : Nat} : Nat → Nat :=
  λ k ↦ b * k

example {b:Nat} {hb : b ≥ 1} :
  ¬ (∃ n, n > 1 ∧ ∀ k, n ∣ (@f b k))
  →
  ∀ n₀, ∃ n ≥ n₀, (@f b n).Prime := by
  intro hc
  by_cases h : b = 1
  subst h

  intro n₀
  unfold f
  simp
  exact Nat.exists_infinite_primes n₀
  exfalso
  contrapose hc
  simp
  exists b
  constructor
  . exact Nat.lt_of_le_of_ne hb fun a ↦ h (id (Eq.symm a))

  . intro k
    unfold f
    exact Nat.dvd_mul_right b k
