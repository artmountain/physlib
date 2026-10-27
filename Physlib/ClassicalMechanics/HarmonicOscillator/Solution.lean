/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaneal Sajan, Joseph Tooby-Smith, Lode Vermeulen
-/

module

public import Physlib.ClassicalMechanics.HarmonicOscillator.Solution.AmplitudePhase
public import Physlib.ClassicalMechanics.HarmonicOscillator.Solution.Energy
public import Physlib.ClassicalMechanics.HarmonicOscillator.Solution.InitialData
public import Physlib.ClassicalMechanics.HarmonicOscillator.Solution.Periodicity
public import Physlib.ClassicalMechanics.HarmonicOscillator.Solution.SpecialPoints
public import Physlib.ClassicalMechanics.HarmonicOscillator.Solution.Uniqueness

/-!

# Solutions to the classical harmonic oscillator

## i. Overview

In this module we define the solutions to the classical harmonic oscillator,
prove that they satisfy the equation of motion, and prove some properties of the solutions.

## ii. Key results

- `InitialConditions` is a structure for the initial conditions for the harmonic oscillator.
- `trajectories` is the trajectories to the harmonic oscillator for given initial conditions.
- `trajectories_equationOfMotion` proves that the solution satisfies the equation of motion.

## iii. Table of contents

- A. A guide to what is in each file

## iv. References

References for the classical harmonic oscillator include:

* Landau & Lifshitz, Mechanics, page 58, section 21. [ref: landau_mechanics]
-/

TODO "Review the namespacing present across files in `./HarmonicOscillator/Solution`, for eg.
trajectory-related declarations currently under InitialConditions could belong in a
trajectory-focused namespace. Identify the affected declarations and downstream API impact before
renaming them."

TODO "Remove this file and split the documentation contained in it across the files in
`./HarmonicOscillator/Solution`"

@[expose] public section

namespace ClassicalMechanics
open Real Time ContDiff

namespace HarmonicOscillator

/-!

## A. A guide to what is in each file

- AmplitudePhase.lean : Amplitude–phase parametrization
  - A. The amplitude–phase initial conditions
  - B. Conversion to standard initial conditions
  - C. The trajectory in normal form
  - D. Recovering the amplitude and phase

- Basic.lean : Basic properties of trajectories
  - A. The trajectory associated with the initial conditions
    - A.1 Definitional equality for the trajectory
  - B. The trajectory for zero initial conditions
  - C. Smoothness of the trajectories
  - D. Velocity of the trajectories
  - E. Acceleration of the trajectories
  - F. The initial conditions of the trajectories
  - G. Trajectories and Equation of motion

- Energy.lean : The energy of the trajectories
  - A. Conservation of energy
  - B. Correctness of InitialConditionsAtTime conversion
  - C. Correctness of InitialConditionsFromTwoPositions conversion
  - D. Correctness of InitialConditionsFromTwoVelocities conversion

- InitialData.lean : The initial conditions
  - A. Definition of the initial conditions
  - B. Relation to other types of initial conditions
    - B.1. Initial conditions at arbitrary time
    - B.2. Initial conditions from two positions at different times
    - B.3. Initial conditions from two velocities at different times
  - C. The zero initial conditions
    - C.1. Simple results for the zero initial conditions

- Periodicity.lean : Periodicity and recurrence
  - A. The period
  - B. Periodicity of the trajectory
  - C. Return to the initial state

- SpecialPoints.lean : Special conditions of the trajectory
  - A. Normal form for standard initial conditions
  - B. Times at which the velocity is zero
  - C. The position when the velocity is zero
  - D. Times at which the trajectory passes through zero

  - Uniqueness.lean : Uniqueness of the solutions
    - A. Uniqueness

-/

end HarmonicOscillator

end ClassicalMechanics
