import Mathlib.Topology.MetricSpace.PiNat
import Mathlib.MeasureTheory.Measure.Hausdorff

/-

In Pauly and Fouche's paper "How constructive is constructing measures?"
in the proof of Example 15 they write:
`let d be the restriction of the usual metric on Cantor space.`

Here we specify what we think they meant by `the usual metric on Cantor space`.
(In an earlier version of this file we did so by hand, but now we just import from Mathlib.)

Speaking of constructing measures, we also include the `Lebesgue measure` on Cantor space.-


-/
noncomputable instance  :
  MetricSpace (ℕ → Bool) :=  PiNat.metricSpaceOfDiscreteUniformity (λ _ ↦ rfl)

noncomputable def μ : MeasureTheory.Measure (ℕ → Bool) := MeasureTheory.Measure.hausdorffMeasure 1
