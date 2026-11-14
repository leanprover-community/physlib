/-
Copyright (c) 2025 Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim. All rights reserved.
Copyright (c) 2026 Sergey A. Cherkis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sergey A. Cherkis, Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim
-/
module

public import Physlib.QFT.Euclidean.GlimmJaffe.Basic

/-!
# Glimm–Jaffe axioms

The measure and generating-functional formulation of the Euclidean field axioms.

## i. Overview

We port the predicates in `OSforGFF/OS/Axioms.lean`: analyticity (OS0), regularity
(OS1), full Euclidean invariance (OS2), complex reflection positivity (OS3), and
ergodicity (OS4). These are assumptions on a probability measure on real tempered distributions;
no existence or reconstruction theorem is asserted.

The source conventions are retained: `d` is the total dimension and `2 ≤ d`;
positive-time tests have topological support in the open positive-time half-space;
OS1 bounds the sum of the integrals of `‖f‖` and `‖f‖^p`; and OS3 asserts
nonnegativity of the real part of the reflected quadratic form. The `p = 2`
condition includes convergence of mollified two-point functions away from zero,
not merely local integrability of a possibly nonexistent limit.

OS4 uses exponentials without a factor of `i`, whereas the characteristic functional
in OS0–OS3 includes that factor.
This numbering differs from the distributional Osterwalder–Schrader axioms E0–E4.

## ii. Key results

* `GlimmJaffeAxioms`: the five Glimm–Jaffe conditions OS0–OS4, with ergodicity as OS4.
* `TwoPointIntegrable`: the explicit mollifier-limit condition at the OS1 endpoint.
* `OS4Ergodicity`: convergence of centered time averages in mean square.

## iii. Table of contents

- A. Analyticity and regularity
- B. Euclidean invariance and reflection positivity
- C. Ergodicity
- D. Bundled axioms

## iv. References

* Glimm and Jaffe, *Quantum Physics*. [ref: glimm1987quantum]
* Cherkis et al., *OSforGFF*, `OS/Axioms.lean`. [ref: osforgff]
-/

@[expose] public section
noncomputable section

open MeasureTheory Filter
open scoped SchwartzMap Topology

namespace GlimmJaffe

variable {d : ℕ} [Fact (2 ≤ d)]

/-! ## A. Analyticity and regularity -/

/-- OS0: the characteristic functional is entire on every finite-dimensional complex
family of Schwartz tests. -/
def OS0Analyticity (μ : ProbabilityMeasure (FieldConfiguration d)) : Prop :=
  ∀ (n : ℕ) (J : Fin n → 𝓢(EuclideanSpacetime d, ℂ)),
    AnalyticOn ℂ (fun z : Fin n → ℂ => generatingFunctional μ (∑ i, z i • J i)) Set.univ

/-- The endpoint condition for OS1: mollified second moments converge at every nonzero
separation to a locally integrable function. No limit is required at coincidence. -/
def TwoPointIntegrable (μ : ProbabilityMeasure (FieldConfiguration d)) : Prop :=
  ∃ K : EuclideanSpacetime d → ℝ, LocallyIntegrable K volume ∧
    ∀ x, x ≠ 0 → Tendsto (fun n =>
      SmearedTwoPointFunction μ (standardBumpSequence (n + 1) (Nat.succ_ne_zero n)) x)
      atTop (𝓝 (K x))

/-- OS1: exponential growth controlled by the integrals of `‖f‖` and `‖f‖^p`,
for some `1 ≤ p ≤ 2`, with the additional two-point condition when `p = 2`. -/
def OS1Regularity (μ : ProbabilityMeasure (FieldConfiguration d)) : Prop :=
  ∃ p c : ℝ, 1 ≤ p ∧ p ≤ 2 ∧ 0 < c ∧
    (∀ f : 𝓢(EuclideanSpacetime d, ℂ),
      ‖generatingFunctional μ f‖ ≤
        Real.exp (c * ((∫ x, ‖f x‖) + ∫ x, ‖f x‖ ^ p))) ∧
    (p = 2 → TwoPointIntegrable μ)

/-! ## B. Euclidean invariance and reflection positivity -/

/-- OS2: invariance of the characteristic functional under the full Euclidean group. -/
def OS2EuclideanInvariance (μ : ProbabilityMeasure (FieldConfiguration d)) : Prop :=
  ∀ (g : EuclideanGroup d) (f : 𝓢(EuclideanSpacetime d, ℂ)),
    generatingFunctional μ f = generatingFunctional μ (euclideanAction g f)

/-- OS3 in the source's complex formulation: the real part of every reflected
quadratic form is nonnegative. Reflection includes complex conjugation of the test. -/
def OS3ReflectionPositivity (μ : ProbabilityMeasure (FieldConfiguration d)) : Prop :=
  ∀ (n : ℕ) (f : Fin n → PositiveTimeTestFunction d) (c : Fin n → ℂ),
    0 ≤ (∑ i, ∑ j, starRingEnd ℂ (c i) * c j *
      generatingFunctional μ ((f i).val - reflectedConjugate (f j).val)).re

/-! ## C. Ergodicity -/

/-- OS4 ergodicity: centered time averages of finite linear combinations of
`exp(⟨ω, f⟩)` converge to zero in mean square. This retains the source's integral
formulation, with the centering inside the time integral. -/
def OS4Ergodicity (μ : ProbabilityMeasure (FieldConfiguration d)) : Prop :=
  ∀ (n : ℕ) (z : Fin n → ℂ) (f : Fin n → 𝓢(EuclideanSpacetime d, ℂ)),
    let A : FieldConfiguration d → ℂ := fun ω => ∑ j, z j * Complex.exp (pairing ω (f j))
    Tendsto (fun T : ℝ =>
      ∫ ω, ‖(1 / T : ℂ) * ∫ s in Set.Icc (0 : ℝ) T,
        (A (timeTranslation s ω) - ∫ ω', A ω' ∂μ.toMeasure)‖ ^ 2 ∂μ.toMeasure)
      atTop (𝓝 0)

/-! ## D. Bundled axioms -/

/-- The Glimm–Jaffe axioms OS0–OS4, with ergodicity as the OS4 condition. -/
structure GlimmJaffeAxioms (μ : ProbabilityMeasure (FieldConfiguration d)) : Prop where
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

end GlimmJaffe
