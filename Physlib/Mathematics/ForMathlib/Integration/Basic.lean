/-
Copyright (c) 2026 Art Mountain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Art Mountain
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
/-!
# Real integrals in multidimensional space

We define lemmas for manipulating integrals over real fields.

-/

@[expose] public section

namespace Integration

open MeasureTheory in
lemma integral_withDensity_ofReal_eq_integral_smul {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : α → ℝ} (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (g : α → E) :
    ∫ x, g x ∂(μ.withDensity fun x => ENNReal.ofReal (f x)) = ∫ x, f x • g x ∂μ := by
  refine (integral_withDensity_eq_integral_smul
    (f := fun x => Real.toNNReal (f x)) hf.real_toNNReal g).trans ?_
  congr 1
  funext x
  rw [NNReal.smul_def, Real.coe_toNNReal _ (hf0 x)]

end Integration
