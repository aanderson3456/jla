import Mathlib.MeasureTheory.Measure.Hausdorff
/-

In `A computational aspect of the Lebesgue differentiation theorem` by NOOPUR PATHAK she writes

`Another characterization of random points in ℝ^d is given by Solovay's Lemma. [...]`
`The proof given by Simpson is given for sets in the Cantor space, but the proof applies here as well.`

Here we expound this by constructing the Cantor-Lebesgue measure on 2^ω using the Lebesgue measure on [0,1].

[A related Marginis entry is that for Miyabe, Nies, Stephan: Randomness and Solovay degrees]

 -/

noncomputable def real_of_cantor : (ℕ → Bool) → ℝ :=
  λ x ↦ tsum (λ n : ℕ ↦ ite (x n = true) ((1:ℝ) / (2 ^ n.succ)) 0)

noncomputable def CantorLebesgueMeasureSubtype : MeasureTheory.Measure (
    {x : ℕ → Bool // ¬ ∃ k, x k = false ∧ ∀ l, k < l → x l = true}
) :=
  MeasureTheory.Measure.comap (λ x ↦ real_of_cantor x.1) MeasureTheory.volume

noncomputable def CantorLebesgueMeasure : MeasureTheory.Measure (ℕ → Bool) :=
  MeasureTheory.Measure.map (λ x ↦ x.1) CantorLebesgueMeasureSubtype

-- using .map thanks to Kevin Buzzard suggestion
