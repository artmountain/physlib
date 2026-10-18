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

- A. The initial conditions
  - A.1. Definition of the initial conditions
  - A.2. Relation to other types of initial conditions
    - A.2.1. Initial conditions at arbitrary time
    - A.2.2. Initial conditions from two positions at different times
    - A.2.3. Initial conditions from two velocities at different times
  - A.3. The zero initial conditions
    - A.3.1. Simple results for the zero initial conditions
- B. Trajectories associated with the initial conditions
  - B.1. The trajectory associated with the initial conditions
    - B.1.1. Definitional equality for the trajectory
  - B.2. The trajectory for zero initial conditions
  - B.3. Smoothness of the trajectories
  - B.4. Velocity of the trajectories
  - B.5. Acceleration of the trajectories
  - B.6. The initial conditions of the trajectories
- C. Trajectories and Equation of motion
  - C.1. Uniqueness of the solutions
- D. The energy of the trajectories
  - D.1. Correctness of InitialConditionsAtTime conversion
  - D.2. Correctness of InitialConditionsFromTwoPositions conversion
  - D.3. Correctness of InitialConditionsFromTwoVelocities conversion
- E. Amplitude–phase parametrization
  - E.1. The amplitude–phase initial conditions
  - E.2. Conversion to standard initial conditions
  - E.3. The trajectory in normal form
  - E.4. Recovering the amplitude and phase
- F. Special conditions of the trajectory
  - F.1. Normal form for standard initial conditions
  - F.2. Times at which the velocity is zero
  - F.3. The position when the velocity is zero
  - F.4. Times at which the trajectory passes through zero
- G. Periodicity and recurrence
  - G.1. The period
  - G.2. Periodicity of the trajectory
  - G.3. Return to the initial state

## iv. References

References for the classical harmonic oscillator include:

* Landau & Lifshitz, Mechanics, page 58, section 21. [ref: landau_mechanics]
-/

@[expose] public section

namespace ClassicalMechanics
open Real Time ContDiff

namespace HarmonicOscillator

end HarmonicOscillator

end ClassicalMechanics
