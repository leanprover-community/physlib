/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import PhyslibAlpha.Mathematics.TauCeti.Analysis.PositiveDefinite.PontryaginMeasure
public import PhyslibAlpha.Mathematics.TauCeti.Analysis.Fourier.Pontryagin.Continuity
public import PhyslibAlpha.Mathematics.TauCeti.Analysis.Fourier.Pontryagin.Uniqueness
public import PhyslibAlpha.Mathematics.TauCeti.Topology.Algebra.PontryaginDual
import PhyslibAlpha.Mathematics.TauCeti.Analysis.Fourier.Pontryagin.StronglyContinuous
import PhyslibAlpha.Mathematics.TauCeti.Analysis.PositiveDefinite.Function.GNS

/-!
# Bochner's theorem on locally compact abelian groups

A positive-definite function `φ` on a locally compact abelian group `G` that is continuous at `0` is
the Fourier–Stieltjes transform `φ(g) = ∫ χ(g) dμ(χ)` of a finite inner regular positive measure `μ`
on the Pontryagin dual of `G`.

## i. Overview

A positive-definite function `φ` on a locally compact abelian group `G` that is continuous at `0`
is the Fourier–Stieltjes transform `φ(g) = ∫ χ(g) dμ(χ)` of a finite inner regular positive
measure `μ` on the Pontryagin dual of `G`.

The representing measure is unique among finite inner regular measures, and conversely the
transform of every such measure is continuous and positive definite. Thus this is a full Bochner
characterization without any countability assumption. When the dual is Polish, every finite Borel
measure is regular, giving the corresponding characterization by arbitrary finite measures. The
dual is Polish when `G` is second countable.

The measure comes from the GNS construction. The function `φ` is a matrix coefficient
`φ(g) = ⟪v, U(-g) v⟫` of the unitary translation representation `U` on its GNS Hilbert space,
which is strongly continuous because `φ` is continuous at `0`. The cyclic spectral theorem for
strongly continuous unitary representations,
`ContRepresentation.exists_pontryaginMeasureTransform_eq_inner`, writes such a matrix coefficient
as a Fourier–Stieltjes transform.

The existence theorem assumes no second countability of `G`, and the GNS space need not be
separable: the integrated form behind the spectral theorem is defined through the inner
regularity of the Haar measure.

## ii. Key results

* `TauCeti.IsPositiveDefiniteSub.exists_pontryaginMeasureTransform_eq_of_continuousAt`: a
  positive-definite function, continuous at `0`, on a locally compact abelian group is the
  Fourier–Stieltjes transform of a finite inner regular measure on the dual group.
* The countability-free Bochner characterization: continuous positive-definite functions are
  precisely the transforms of unique finite inner regular measures.
* `TauCeti.continuous_and_isPositiveDefiniteSub_iff_existsUnique_pontryaginMeasureTransform_eq`:
  the full Bochner characterization by unique finite measures on a locally compact abelian
  group with Polish dual.

## iii. Table of contents

- A. Development

## iv. References

* G. B. Folland, *A Course in Abstract Harmonic Analysis*, 2nd ed., CRC Press (2016),
  Theorem 4.18.
-/

public section

/-! ## A. Development -/

open MeasureTheory

namespace TauCeti

variable {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
  [LocallyCompactSpace G]
  [MeasurableSpace (PontryaginDual (Multiplicative G))]
  [BorelSpace (PontryaginDual (Multiplicative G))]

/-- **Bochner's theorem on a locally compact abelian group**, existence half.
A positive-definite function that is continuous at `0` is the Fourier–Stieltjes transform of a
finite inner regular measure on the Pontryagin dual. -/
lemma IsPositiveDefiniteSub.exists_pontryaginMeasureTransform_eq_of_continuousAt {φ : G → ℂ}
    (hφ : IsPositiveDefiniteSub φ) (hφ₀ : ContinuousAt φ 0) :
    ∃ μ : FiniteMeasure (PontryaginDual (Multiplicative G)),
      μ.toMeasure.InnerRegular ∧ μ.pontryaginMeasureTransform = φ := by
  -- `φ g = ⟪U(g) v, v⟫ = ⟪v, U(-g) v⟫` for the GNS representation `U` and the vector `v` at `0`,
  -- so `φ` is a matrix coefficient of the representation `g ↦ U(-g)`.
  let π : ContRepresentation ℂ (Multiplicative G) hφ.gnsSpace := .ofMonoidHom <|
    (unitary _).subtype.comp <|
      Unitary.linearIsometryEquiv.symm.toMonoidHom.comp (hφ.gnsRepresentation.comp invMonoidHom)
  have hπ_apply (g : G) (v : hφ.gnsSpace) : π (.ofAdd g) v = hφ.gnsTranslation (-g) v := by
    rw [← ContRepresentation.toMonoidHom_apply]
    simp [π, ← ofAdd_neg]
  have hπ : ContRepresentation.IsUnitary π :=
    (ContRepresentation.isUnitary_iff_mem_unitary π).mpr fun g ↦ Subtype.prop _
  have hcont (v : hφ.gnsSpace) : Continuous fun g : G ↦ π (.ofAdd g) v := by
    simp_rw [hπ_apply]
    exact (hφ.continuous_gnsTranslation_apply hφ₀ v).comp continuous_neg
  obtain ⟨μ, hμreg, hμ⟩ := π.exists_pontryaginMeasureTransform_eq_inner hcont hπ (hφ.gnsVector 0)
  refine ⟨μ, hμreg, funext fun g ↦ ?_⟩
  rw [hμ, hπ_apply, ← hφ.gnsRepresentation_ofAdd, hφ.gnsRepresentation_gnsVector, add_zero,
    hφ.inner_gnsVector, zero_sub, neg_neg]

/-- **Unique inner regular form of Bochner's theorem.** A positive-definite function continuous at
`0` has a unique finite inner regular representing measure on the Pontryagin dual. No countability
or metrizability assumption is needed. -/
lemma
    IsPositiveDefiniteSub.existsUnique_innerRegular_pontryaginMeasureTransform_eq_of_continuousAt
    {φ : G → ℂ} (hφ : IsPositiveDefiniteSub φ) (hφ₀ : ContinuousAt φ 0) :
    ∃! μ : FiniteMeasure (PontryaginDual (Multiplicative G)),
      μ.toMeasure.InnerRegular ∧ μ.pontryaginMeasureTransform = φ := by
  obtain ⟨μ, hμreg, hμ⟩ := hφ.exists_pontryaginMeasureTransform_eq_of_continuousAt hφ₀
  refine ⟨μ, ⟨hμreg, hμ⟩, fun ν hν ↦ ?_⟩
  exact FiniteMeasure.pontryaginMeasureTransform_injOn_innerRegular hν.1 hμreg
    (hν.2.trans hμ.symm)

/-- **Bochner's characterization without countability assumptions.** A function on a locally
compact abelian group is continuous and positive definite if and only if it is the
Fourier–Stieltjes transform of a unique finite inner regular measure on the Pontryagin dual. -/
lemma
    continuous_and_isPositiveDefiniteSub_iff_existsUnique_innerRegular_pontryaginMeasureTransform_eq
    (φ : G → ℂ) :
    (Continuous φ ∧ IsPositiveDefiniteSub φ) ↔
      ∃! μ : FiniteMeasure (PontryaginDual (Multiplicative G)),
        μ.toMeasure.InnerRegular ∧ μ.pontryaginMeasureTransform = φ := by
  constructor
  · rintro ⟨hcont, hφ⟩
    exact hφ.existsUnique_innerRegular_pontryaginMeasureTransform_eq_of_continuousAt
      hcont.continuousAt
  · rintro ⟨μ, ⟨hμreg, rfl⟩, -⟩
    let _ : μ.toMeasure.InnerRegular := hμreg
    exact ⟨μ.continuous_pontryaginMeasureTransform
        isTightMeasureSet_singleton_of_innerRegular,
      μ.isPositiveDefiniteSub_pontryaginMeasureTransform⟩

/-- **Bochner's characterization on a locally compact abelian group with Polish dual.** A
function is continuous and positive definite if and only if it is the Fourier–Stieltjes
transform of a unique finite positive Borel measure on the dual group. The dual is Polish when
the group is second countable. -/
lemma continuous_and_isPositiveDefiniteSub_iff_existsUnique_pontryaginMeasureTransform_eq
    [PolishSpace (PontryaginDual (Multiplicative G))] (φ : G → ℂ) :
    (Continuous φ ∧ IsPositiveDefiniteSub φ) ↔
      ∃! μ : FiniteMeasure (PontryaginDual (Multiplicative G)),
        μ.pontryaginMeasureTransform = φ := by
  constructor
  · rintro ⟨hcont, hφ⟩
    obtain ⟨μ, -, hμ⟩ := hφ.exists_pontryaginMeasureTransform_eq_of_continuousAt hcont.continuousAt
    refine ⟨μ, hμ, fun ν hν ↦ ?_⟩
    exact FiniteMeasure.pontryaginMeasureTransform_injective (hν.trans hμ.symm)
  · rintro ⟨μ, rfl, _⟩
    exact ⟨μ.continuous_pontryaginMeasureTransform isTightMeasureSet_singleton,
      μ.isPositiveDefiniteSub_pontryaginMeasureTransform⟩

end TauCeti
