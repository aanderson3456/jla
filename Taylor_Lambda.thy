theory Taylor_Lambda
imports QML Main

(* In Paul Taylor's article "A lambda calculus for real analysis", Proposition 2.16 mentions the modal schema below.
  We prove that it is valid in the context of the package QML (Quantified Modal Logic), i.e., standard Kripke semantics with no additional axioms.
*)

begin

abbreviation Taylor  where "Taylor ≡ ❙∀φ. ❙∀ ψ .  ❙□φ ❙→ (❙◇ ψ ❙→  ❙◇ (ψ ❙∧ φ))"

lemma "⌊Taylor⌋"
  by blast

end
