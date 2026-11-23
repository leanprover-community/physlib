/-
Copyright (c) 2026 Sergey A. Cherkis, Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sergey A. Cherkis, Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim
-/
module

public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Physlib.QFT.Euclidean.GlimmJaffe.FieldConfiguration
public import Physlib.SpaceAndTime.TimeAndSpace.TestFunctions.Schwartz

/-!
# Glimm–Jaffe Euclidean fields

Generating functionals and Schwinger functions for a real scalar field.

## i. Overview

This is the measure-based formulation of a real scalar Euclidean quantum field.
A field configuration, defined in `FieldConfiguration`, is a tempered distribution `ω`,
so the basic observable is its evaluation `ω f` on a real Schwartz test function `f`.
A probability measure on these configurations specifies the field statistics, in a way that
Schwinger functions are expectations of products of field evaluations, and the
generating functional is the expectation of `exp(i ⟨ω, f⟩)`. The Glimm–Jaffe axioms
in the companion file impose analyticity, growth bounds, Euclidean invariance,
reflection positivity and ergodicity on this measure. This setup supplies the
Euclidean data for reconstruction.

The parameter `d` counts spatial dimensions. Spacetime is Physlib's
`TimeAndSpace d = Time × Space d`, with the standard origins used by its real
vector-space instances. Thus the source's total dimension is `d + 1`.

The Euclidean symmetries, positive-time tests and normalized bumps acting on the
test functions are in `TimeAndSpace.TestFunctions.Schwartz`.

## ii. Key results

* `FieldMeasure.generatingFunctional`: the complex characteristic functional.
* `smearedTwoPointFunction`: the two-point function smeared with an arbitrary normalized bump.

## iii. Table of contents

- A. Generating functionals
- B. Schwinger functions

## iv. References

* Glimm and Jaffe, *Quantum Physics*. [ref: glimm1987quantum]
-/

@[expose] public section
noncomputable section

open MeasureTheory TimeAndSpace
open scoped SchwartzMap

namespace GlimmJaffe

variable {d : ℕ}

/-- A probability measure on field configurations.
  The Euclidean functional-integral measure `μ`, the rigorous counterpart of `𝒟φ e^{-S}/Z`. -/
abbrev FieldMeasure (d : ℕ) : Type := ProbabilityMeasure (FieldConfiguration d)

namespace FieldMeasure

open FieldConfiguration

/-! ## A. Generating functionals -/

/-- The characteristic functional `Z[f] = ∫ exp(i ⟨ω, f⟩) dμ` on complex tests. -/
def generatingFunctional (μ : FieldMeasure d)
    (f : 𝓢(TimeAndSpace d, ℂ)) : ℂ :=
  ∫ ω, Complex.exp (Complex.I * pairing ω f) ∂μ.toMeasure

/-! ## B. Schwinger functions -/

/-- The real `n`-point Schwinger function, the expectation of the product of field evaluations. -/
def schwingerFunction (μ : FieldMeasure d) (n : ℕ) (f : Fin n → 𝓢(TimeAndSpace d, ℝ)) : ℝ :=
  ∫ ω, (∏ i, ω (f i)) ∂μ.toMeasure

/-- The real two-point Schwinger function evaluated on two Schwartz tests. -/
def schwingerFunction₂ (μ : FieldMeasure d) (f g : 𝓢(TimeAndSpace d, ℝ)) : ℝ :=
  schwingerFunction μ 2 ![f, g]

/-- The two-point Schwinger function smeared at `x` and zero with an arbitrary normalized bump.
This follows `SmearedTwoPointFunction` in `OSforGFF`, with the bump supplied independently
of the standard sequence used in the OS1 endpoint condition. -/
def smearedTwoPointFunction (μ : FieldMeasure d)
    (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin (d + 1)))) (x : TimeAndSpace d) : ℝ :=
  schwingerFunction₂ μ
    (SchwartzMap.postcompCLM Complex.reCLM
      (translateSchwartz (SchwartzMap.postcompCLM Complex.ofRealCLM (bumpToSchwartz φ)) x))
    (bumpToSchwartz φ)

end FieldMeasure

end GlimmJaffe
