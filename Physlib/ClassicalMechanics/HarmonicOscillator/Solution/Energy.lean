/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaneal Sajan, Joseph Tooby-Smith, Lode Vermeulen
-/
module

public import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import Physlib.ClassicalMechanics.HarmonicOscillator.Solution.Basic
public import Physlib.ClassicalMechanics.HarmonicOscillator.Solution.InitialData

/-!

# The energy of the trajectories

## i. Overview

The state of the harmonic oscillator at `t = 0` is captured by `InitialConditions` as a position
`x₀` and a velocity `v₀`. An equivalent and often more physical description writes the solution as
a single shifted cosine of amplitude `A` and phase `φ`:
  `x(t) = A cos (ω t - φ)`.

Expanding with the angle-subtraction identity,
  `A cos (ω t - φ) = (A cos φ) cos (ω t) + (A sin φ) sin (ω t)`,
and matching coefficients against the standard solution
  `x(t) = cos (ω t) x₀ + (sin (ω t) / ω) v₀`
gives the change of coordinates
  `x₀ = A cos φ`,   `v₀ = A ω sin φ`.

We implement the forward map `(A, φ) ↦ (x₀, v₀)` as `toInitialConditions`, prove the resulting
trajectory is the cosine normal form above (with velocity `-A ω sin (ω t - φ)`), and implement the
inverse map `(x₀, v₀) ↦ (A, φ)` as `fromInitialConditions`, recovering `A` and `φ` as the polar
coordinates of the phase vector `(x₀, v₀ / ω)`.

## ii. Key results

## iii. Table of contents
- A. Conservation of energy

## iv. References

References for the classical harmonic oscillator include:

* Landau & Lifshitz, Mechanics, page 58, section 21. [ref: landau_mechanics]
-/

@[expose] public

noncomputable section

open Real Time ContDiff

variable (S : HarmonicOscillator)

namespace ClassicalMechanics.HarmonicOscillator

/-!

## A. Conservation of energy

For a given set of initial conditions, the energy of the trajectory is constant,
due to the conservation of energy. Here we show it's value.

-/
lemma trajectory_energy (IC : InitialConditions) : S.energy (IC.trajectory S) =
    fun _ => 1/2 * (S.m * ‖IC.v₀‖ ^2 + S.k * ‖IC.x₀‖ ^ 2) := by
  funext t
  rw [energy_conservation_of_equationOfMotion' _ _ (by fun_prop) (InitialConditions.trajectory_equationOfMotion S IC)]
  simp [energy, kineticEnergy, potentialEnergy]
  ring_nf

end HarmonicOscillator

end ClassicalMechanics
