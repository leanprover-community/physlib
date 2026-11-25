/-
Copyright (c) 2026 Sergey A. Cherkis, Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sergey A. Cherkis, Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim
-/
module

public import Mathlib.Analysis.Normed.Module.WeakDual
public import Physlib.QFT.Euclidean.GlimmJaffe.Basic
public import Physlib.QFT.Euclidean.GlimmJaffe.StandardBump

/-!
# Glimm–Jaffe axioms

The measure and generating-functional formulation of the Euclidean field axioms.

## i. Overview

This is a formalization of the Glimm–Jaffe variation of the Osterwalder–Schrader axioms,
as presented in Glimm and Jaffe, *Quantum Physics*, Chapter 6. [ref: glimm1987quantum]
This formalism is on the generating functional, while the original OS axioms are on the
Schwinger functions.

We port the predicates in `OSforGFF/OS/Axioms.lean`: analyticity (OS0), regularity
(OS1), full Euclidean invariance (OS2), complex reflection positivity (OS3), and
ergodicity (OS4).

Here `d` counts spatial dimensions, so the source total dimension is `d + 1`.
Reflection positivity, ergodicity and the bundle assume `1 ≤ d`, retaining the source
minimum of two total dimensions.

OS4 uses exponentials without a factor of `i`, whereas the characteristic functional
in OS0–OS3 includes that factor.
This numbering differs from the distributional Osterwalder–Schrader axioms E0–E4.

## ii. Key results

* `FieldMeasure.GlimmJaffeAxioms`: the five Glimm–Jaffe conditions OS0–OS4, with ergodicity
  as OS4.
* `FieldMeasure.TwoPointIntegrable`: the explicit mollifier-limit condition at the OS1 endpoint.
* `FieldMeasure.OS4Ergodicity`: convergence of centered time averages in mean square.

## iii. Table of contents

- A. Analyticity and regularity
- B. Euclidean invariance and reflection positivity
- C. Ergodicity
- D. Bundled axioms

## iv. References

* Glimm and Jaffe, *Quantum Physics*, Chapter 6. [ref: glimm1987quantum]
* Cherkis et al., *OSforGFF*, `OS/Axioms.lean`. [ref: osforgff]
-/

@[expose] public section
noncomputable section

open MeasureTheory Filter
open scoped SchwartzMap Topology

namespace GlimmJaffe

namespace FieldMeasure

open FieldConfiguration TimeAndSpace

variable {d : ℕ}

/-! ## A. Analyticity and regularity -/

/-- OS0: the characteristic functional is entire on every finite-dimensional complex
family of Schwartz tests. -/
def OS0Analyticity (μ : FieldMeasure d) : Prop :=
  ∀ (n : ℕ) (J : Fin n → 𝓢(TimeAndSpace d, ℂ)),
    AnalyticOn ℂ (fun z : Fin n → ℂ => generatingFunctional μ (∑ i, z i • J i)) Set.univ

/-- The endpoint condition for OS1: mollified second moments converge at every nonzero
separation to a locally integrable function. No limit is required at coincidence. -/
def TwoPointIntegrable (μ : FieldMeasure d) : Prop :=
  ∃ K : TimeAndSpace d → ℝ, LocallyIntegrable K volume ∧
    ∀ x, x ≠ 0 → Tendsto (fun n =>
      smearedTwoPointFunction μ (standardBumpSequence (n + 1) (Nat.succ_ne_zero n)) x)
      atTop (𝓝 (K x))

/-- OS1: exponential growth controlled by the integrals of `‖f‖` and `‖f‖^p`,
for some `1 ≤ p ≤ 2`, with the additional two-point condition when `p = 2`. -/
def OS1Regularity (μ : FieldMeasure d) : Prop :=
  ∃ p c : ℝ, 1 ≤ p ∧ p ≤ 2 ∧ 0 < c ∧
    (∀ f : 𝓢(TimeAndSpace d, ℂ),
      ‖generatingFunctional μ f‖ ≤
        Real.exp (c * ((∫ x, ‖f x‖) + ∫ x, ‖f x‖ ^ p))) ∧
    (p = 2 → TwoPointIntegrable μ)

/-! ## B. Euclidean invariance and reflection positivity -/

/-- OS2: invariance of the characteristic functional under the full Euclidean group. -/
def OS2EuclideanInvariance (μ : FieldMeasure d) : Prop :=
  ∀ (g : EuclideanGroup (d + 1)) (f : 𝓢(TimeAndSpace d, ℂ)),
    generatingFunctional μ f = generatingFunctional μ (schwartzSpacetimeEuclideanAction g f)

/-- OS3 in the source's complex formulation: the real part of every reflected
quadratic form is nonnegative. Reflection includes complex conjugation of the test.
The dimension assumption retains the source's requirement of at least one spatial dimension. -/
@[nolint unusedArguments]
def OS3ReflectionPositivity [Fact (1 ≤ d)] (μ : FieldMeasure d) : Prop :=
  ∀ (n : ℕ) (f : Fin n → PositiveTimeTestFunction d) (c : Fin n → ℂ),
    0 ≤ (∑ i, ∑ j, starRingEnd ℂ (c i) * c j *
      generatingFunctional μ ((f i).val - reflectedConjugate (f j).val)).re

/-! ## C. Ergodicity -/

/-- OS4 ergodicity: centered time averages of finite linear combinations of
`exp(⟨ω, f⟩)` converge to zero in mean square. This retains the source's integral
formulation, with the centering inside the time integral. The dimension restriction retains
the source's domain of at least two total dimensions. -/
def OS4Ergodicity [Fact (1 ≤ d)] (μ : FieldMeasure d) : Prop :=
  ∀ (n : ℕ) (z : Fin n → ℂ) (f : Fin n → 𝓢(TimeAndSpace d, ℂ)),
    let A : WeakDual ℂ (𝓢(TimeAndSpace d, ℂ)) → ℂ :=
      fun η => ∑ j, z j * Complex.exp (η (f j))
    Tendsto (fun T : ℝ =>
      ∫ ω, ‖(1 / T : ℂ) * ∫ s in Set.Icc (0 : ℝ) T,
        (A (timeTranslation s (pairing ω)) - ∫ ω', A (pairing ω') ∂μ.toMeasure)‖ ^ 2
        ∂μ.toMeasure)
      atTop (𝓝 0)

/-! ## D. Bundled axioms -/

/-- The Glimm–Jaffe axioms OS0–OS4, with ergodicity as the OS4 condition. -/
structure GlimmJaffeAxioms [Fact (1 ≤ d)] (μ : FieldMeasure d) : Prop where
  /-- OS0: entire dependence on finite families of complex tests. -/
  analytic : OS0Analyticity μ
  /-- OS1: the exponential bound and endpoint two-point condition. -/
  regular : OS1Regularity μ
  /-- OS2: full Euclidean invariance. -/
  euclideanInvariant : OS2EuclideanInvariance μ
  /-- OS3: reflection positivity for complex positive-time tests and coefficients. -/
  reflectionPositive : OS3ReflectionPositivity μ
  /-- OS4: mean-square ergodicity under time translation. -/
  ergodic : OS4Ergodicity μ

end FieldMeasure

end GlimmJaffe
