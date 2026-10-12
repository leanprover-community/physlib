/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import PhyslibAlpha.Mathematics.TauCeti.Analysis.PositiveDefinite.PontryaginMeasure
import PhyslibAlpha.Mathematics.TauCeti.Analysis.Bochner.LocallyCompactGroup

/-!
# Bochner's theorem on discrete abelian groups

A function `φ` on a discrete abelian group `G` is positive definite, `∑ᵢ ∑ⱼ cᵢ conj(cⱼ) φ(gᵢ - gⱼ) ≥
0` for every finite family, if and only if it is the Fourier–Stieltjes transform `φ(g) = ∫ χ(g)
dμ(χ)` of a finite inner regular positive measure `μ` on the Pontryagin dual of `G`.

## i. Overview

A function `φ` on a discrete abelian group `G` is positive definite,
`∑ᵢ ∑ⱼ cᵢ conj(cⱼ) φ(gᵢ - gⱼ) ≥ 0` for every finite family, if and only if it is the
Fourier–Stieltjes transform `φ(g) = ∫ χ(g) dμ(χ)` of a finite inner regular positive measure `μ`
on the Pontryagin dual of `G`. Every function on a discrete group is continuous, so no
continuity hypothesis appears.

The representing measure is the one of Bochner's theorem on locally compact abelian groups,
`TauCeti.IsPositiveDefiniteSub.exists_pontryaginMeasureTransform_eq_of_continuousAt`, whose
continuity hypothesis is automatic on a discrete group.

For `G = ℤ` this recovers Herglotz's theorem, proved separately by Fejér means in
`TauCeti.Analysis.Bochner.Herglotz`.

## ii. Key results

* `TauCeti.isPositiveDefiniteSub_iff_exists_pontryaginMeasureTransform_eq`: **Bochner's theorem**
  for discrete abelian groups.

## iii. Table of contents

- A. Development

## iv. References

* W. Rudin, *Fourier Analysis on Groups*, Interscience (1962), §1.4.
* G. B. Folland, *A Course in Abstract Harmonic Analysis*, 2nd ed., CRC Press (2016), §3.3
  and §4.2.
-/

public section

/-! ## A. Development -/

open MeasureTheory

namespace TauCeti

variable {G : Type*} [AddCommGroup G] [TopologicalSpace G] [DiscreteTopology G]
  [MeasurableSpace (PontryaginDual (Multiplicative G))]
  [BorelSpace (PontryaginDual (Multiplicative G))]

/-- **Bochner's theorem on a discrete abelian group.** A function on a discrete abelian group is
positive definite if and only if it is the Fourier–Stieltjes transform of a finite inner regular
measure on the Pontryagin dual. -/
lemma isPositiveDefiniteSub_iff_exists_pontryaginMeasureTransform_eq (φ : G → ℂ) :
    IsPositiveDefiniteSub φ ↔
      ∃ μ : FiniteMeasure (PontryaginDual (Multiplicative G)),
        μ.toMeasure.InnerRegular ∧ μ.pontryaginMeasureTransform = φ :=
  ⟨fun hφ ↦ hφ.exists_pontryaginMeasureTransform_eq_of_continuousAt
      continuous_of_discreteTopology.continuousAt,
    fun ⟨μ, _, hμ⟩ ↦ hμ ▸ μ.isPositiveDefiniteSub_pontryaginMeasureTransform⟩

end TauCeti
