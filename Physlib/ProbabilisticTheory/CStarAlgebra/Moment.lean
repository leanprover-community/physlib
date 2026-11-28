/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
public import Physlib.Mathematics.Calculus.Exponential
public import Physlib.ProbabilisticTheory.CStarAlgebra.State

/-!
# Moments of observables

The moments of an observable in a state, and the characteristic function they come from.

## i. Overview

A state `ω` gives each observable `a` its moments `ω (aⁿ)`. The first moment is the mean `ω a`.
The central moments are the moments of the centered observable `a - ω a`.

Every observable `a` generates the unitary one-parameter group `t ↦ exp (i t a)`. The
characteristic function of `a` in `ω` is `t ↦ ω (exp (i t a))`. Its `n`-th derivative at `0` is
`iⁿ` times the `n`-th moment.

## ii. Key results

- `ProbabilisticTheory.State.centered` : an observable minus its mean.
- `ProbabilisticTheory.State.moment`, `ProbabilisticTheory.State.centralMoment` : the moments and
  the central moments of an observable.
- `ProbabilisticTheory.State.charFun` : the characteristic function of an observable.
- `ProbabilisticTheory.State.iteratedDeriv_charFun_zero` : the derivatives of the characteristic
  function at `0` are the moments.

## iii. Table of contents

- A. Centered observables
- B. Moments
- C. The characteristic function

## iv. References

* None.

-/

@[expose] public section

open scoped ComplexOrder

namespace ProbabilisticTheory.State

variable {𝒜 : Type*} [CStarAlgebra 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜]

/-! ## A. Centered observables -/

/-- The observable `a` minus its mean in the state `ω`. -/
noncomputable def centered (ω : (ofCStarAlgebra 𝒜).State) (a : selfAdjoint 𝒜) : selfAdjoint 𝒜 :=
  a - ω a • 1

/-- A centered observable has mean zero. -/
@[simp]
lemma apply_centered (ω : (ofCStarAlgebra 𝒜).State) (a : selfAdjoint 𝒜) : ω (ω.centered a) = 0 := by
  simp [centered]

/-- The centered observable as an operator. -/
lemma coe_centered (ω : (ofCStarAlgebra 𝒜).State) (a : selfAdjoint 𝒜) :
    (ω.centered a : 𝒜) = a - (ω a : ℂ) • 1 := by
  simp [centered, Complex.coe_smul]

/-! ## B. Moments -/

/-- The `n`-th moment of an observable, the value of `ω` on its `n`-th power. -/
noncomputable def moment (ω : (ofCStarAlgebra 𝒜).State) (a : selfAdjoint 𝒜) (n : ℕ) : ℝ :=
  ω ⟨(a : 𝒜) ^ n, a.2.pow n⟩

/-- The `n`-th central moment of an observable, the moment of its centered observable. -/
noncomputable def centralMoment (ω : (ofCStarAlgebra 𝒜).State) (a : selfAdjoint 𝒜) (n : ℕ) :
    ℝ :=
  ω.moment (ω.centered a) n

/-- The moments are the values of `ω` on the powers of the observable. -/
lemma coe_moment (ω : (ofCStarAlgebra 𝒜).State) (a : selfAdjoint 𝒜) (n : ℕ) :
    (ω.moment a n : ℂ) = ω.extend ((a : 𝒜) ^ n) :=
  (extend_apply ω _).symm

/-- The first moment is the mean. -/
@[simp]
lemma moment_one (ω : (ofCStarAlgebra 𝒜).State) (a : selfAdjoint 𝒜) : ω.moment a 1 = ω a := by
  simp [moment]

/-- The first central moment vanishes. -/
@[simp]
lemma centralMoment_one (ω : (ofCStarAlgebra 𝒜).State) (a : selfAdjoint 𝒜) :
    ω.centralMoment a 1 = 0 := by
  rw [centralMoment, moment_one, apply_centered]

/-! ## C. The characteristic function -/

/-- The characteristic function `t ↦ ω (exp (i t a))` of an observable `a` in the state `ω`. -/
noncomputable def charFun (ω : (ofCStarAlgebra 𝒜).State) (a : selfAdjoint 𝒜) (t : ℝ) : ℂ :=
  ω.extend (NormedSpace.exp (t • (Complex.I • (a : 𝒜))))

/-- The `n`-th derivative of the characteristic function at `0` is `iⁿ` times the `n`-th
moment. -/
lemma iteratedDeriv_charFun_zero (ω : (ofCStarAlgebra 𝒜).State) (a : selfAdjoint 𝒜) (n : ℕ) :
    iteratedDeriv n (ω.charFun a) 0 = Complex.I ^ n * ω.moment a n := by
  refine (((⟨ω.extend.toLinearMap, map_continuous ω.extend⟩ : 𝒜 →L[ℂ] ℂ).restrictScalars
    ℝ).iteratedDeriv_comp_exp_smul_const_zero (Complex.I • (a : 𝒜)) n).trans ?_
  rw [coe_moment, smul_pow]
  exact map_smul ω.extend _ _

end ProbabilisticTheory.State
