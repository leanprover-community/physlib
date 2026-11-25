/-
Copyright (c) 2026 Sergey A. Cherkis, Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sergey A. Cherkis, Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Physlib.SpaceAndTime.Space.EuclideanGroup.AffineGroup
public import Physlib.SpaceAndTime.TimeAndSpace.Basic

/-!
# Schwartz test functions on time and space

Euclidean symmetries, positive-time support, bumps and translations of Schwartz tests.

## i. Overview

Schwartz functions on `TimeAndSpace d` are the test functions of Euclidean field theory.
The full `EuclideanGroup (d + 1)` acts on them by pullback, transported through
time-first Euclidean coordinates, so it includes transformations mixing time and space.
The reflected conjugate combines complex conjugation with time reflection, and
positive-time test functions are those supported strictly at positive time.

Normalized smooth bumps are constructed in Euclidean coordinates and pulled back to
`TimeAndSpace d`, keeping integral one.

## ii. Key results

* `TimeAndSpace.schwartzSpacetimeEuclideanAction`: the full spacetime Euclidean group
  `EuclideanGroup (d + 1)` acting on complex tests, as opposed to the spatial
  `schwartzEuclideanAction`.
* `TimeAndSpace.reflectedConjugate`: conjugation combined with Euclidean time reflection.
* `TimeAndSpace.PositiveTimeTestFunction`: complex tests supported at positive time.
* `TimeAndSpace.bumpToSchwartz`: a normalized bump as a real Schwartz test.

## iii. Table of contents

- A. Euclidean symmetries and positive time
- B. Bumps and translations

## iv. References

* Glimm and Jaffe, *Quantum Physics*. [ref: glimm1987quantum]
* Cherkis et al., *OSforGFF*. [ref: osforgff]
-/

@[expose] public section
noncomputable section

open MeasureTheory
open scoped SchwartzMap

namespace TimeAndSpace

variable {d : ℕ}

/-! ## A. Euclidean symmetries and positive time -/

/-- Pullback by a full Euclidean transformation, including rotations mixing time and space. -/
def schwartzSpacetimeEuclideanAction (g : EuclideanGroup (d + 1)) :
    𝓢(TimeAndSpace d, ℂ) →L[ℂ] 𝓢(TimeAndSpace d, ℂ) :=
  let e := TimeAndSpace.euclideanCoordinates (d := d)
  let a := EuclideanGroup.toAffineIsometryHom g⁻¹
  let pullback := SchwartzMap.compCLMOfAntilipschitz ℂ (K := 1)
    (g := fun x => a.linearIsometryEquiv x + a 0)
    (a.linearIsometryEquiv.toContinuousLinearMap.hasTemperateGrowth.add (by fun_prop))
    (by
      have ha : (fun x => a.linearIsometryEquiv x + a 0) = a := by
        funext x
        simpa only [vadd_eq_add, add_zero] using (a.map_vadd 0 x).symm
      rw [ha]
      exact a.antilipschitzWith)
  (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e).comp
    (pullback.comp (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e.symm))

/-- The full Euclidean pullback expressed in time-first coordinates. -/
@[simp]
lemma schwartzSpacetimeEuclideanAction_apply (g : EuclideanGroup (d + 1))
    (f : 𝓢(TimeAndSpace d, ℂ)) (x : TimeAndSpace d) :
    schwartzSpacetimeEuclideanAction g f x = f (TimeAndSpace.euclideanCoordinates.symm
      (EuclideanGroup.toAffineIsometryHom g⁻¹ (TimeAndSpace.euclideanCoordinates x))) := by
  change f (TimeAndSpace.euclideanCoordinates.symm (_ + _)) = _
  congr 2
  simpa only [ContinuousLinearEquiv.coe_coe, vadd_eq_add, add_zero] using
    ((EuclideanGroup.toAffineIsometryHom g⁻¹).map_vadd 0
      (TimeAndSpace.euclideanCoordinates x)).symm

/-- Complex conjugation after time reflection, `f ↦ (x ↦ conj (f (Θ x)))`,
in any spatial dimension. -/
@[nolint unusedArguments]
def reflectedConjugate (f : 𝓢(TimeAndSpace d, ℂ)) :
    𝓢(TimeAndSpace d, ℂ) :=
  SchwartzMap.postcompCLM Complex.conjCLE.toContinuousLinearMap
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℝ TimeAndSpace.timeReflection f)

/-- The reflected conjugate includes both time reflection and complex conjugation. -/
@[simp]
lemma reflectedConjugate_apply (f : 𝓢(TimeAndSpace d, ℂ))
    (x : TimeAndSpace d) :
    reflectedConjugate f x = starRingEnd ℂ (f (TimeAndSpace.timeReflection x)) := rfl

/-- Applying the reflected conjugation twice recovers the original test. -/
@[simp]
lemma reflectedConjugate_involutive (f : 𝓢(TimeAndSpace d, ℂ)) :
    reflectedConjugate (reflectedConjugate f) = f := by
  ext x
  simp only [reflectedConjugate_apply, starRingEnd_self_apply,
    TimeAndSpace.timeReflection_involutive]

/-- Complex Schwartz functions whose topological support lies strictly at positive time.
This uses the support convention of `OSforGFF` in any spatial dimension. -/
@[nolint unusedArguments]
abbrev PositiveTimeTestFunction (d : ℕ) :=
  {f : 𝓢(TimeAndSpace d, ℂ) | tsupport f ⊆ {x | 0 < x.1}}

/-! ## B. Bumps and translations -/

/-- Convert a smooth bump centered at zero to a real Schwartz test with integral one. -/
def bumpToSchwartz (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin (d + 1)))) :
    𝓢(TimeAndSpace d, ℝ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℝ TimeAndSpace.euclideanCoordinates
    ((φ.hasCompactSupport_normed (μ := volume)).toSchwartzMap φ.contDiff_normed)

/-- The Euclidean bump retains integral one after transport to time and space coordinates. -/
@[simp]
lemma integral_bumpToSchwartz (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin (d + 1)))) :
    ∫ x, bumpToSchwartz φ x = 1 := by
  change ∫ x, φ.normed volume (TimeAndSpace.euclideanCoordinates x) = 1
  rw [TimeAndSpace.euclideanCoordinates_measurePreserving.integral_comp
    TimeAndSpace.euclideanCoordinates.toHomeomorph.measurableEmbedding]
  exact φ.integral_normed

/-- Translate a complex Schwartz test by `a`, with value `f (x - a)` at `x`. -/
def translateSchwartz (f : 𝓢(TimeAndSpace d, ℂ))
    (a : TimeAndSpace d) : 𝓢(TimeAndSpace d, ℂ) :=
  SchwartzMap.compSubConstCLM ℂ a f

end TimeAndSpace
