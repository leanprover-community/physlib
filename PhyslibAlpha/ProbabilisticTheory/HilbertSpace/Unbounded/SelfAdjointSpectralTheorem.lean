/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ProbabilisticTheory.HilbertSpace.Unbounded.RealAnalytic
public import PhyslibAlpha.ProbabilisticTheory.HilbertSpace.Unbounded.StoneUnitaryGroup
public import PhyslibAlpha.ProbabilisticTheory.HilbertSpace.Unbounded.WeakIntegral

/-!

# The spectral theorem, stated

Essential self-adjointness and spectral resolutions of self-adjoint operators, with their domains.

## i. Overview

An operator is essentially self-adjoint when its closure is self-adjoint; a self-adjoint extension
is then unique. A spectral measure `μ` on `ℝ` resolves a self-adjoint operator `T` when `⟪y, T x⟫ =
∫ λ d⟪y, μ x⟫` for `x` in the domain of `T`, and it resolves `T` with its domain when in addition
the domain of `T` is the set of vectors with `∫ λ² dμₓ < ∞`.

## ii. Key results

- `SelfAdjointClosureData` : an operator with self-adjoint closure.
- `SelfAdjointClosureData.unique_selfAdjoint_extension` : the self-adjoint extension is unique.
- `IsWeakSpectralResolution` : `⟪y, T x⟫ = ∫ λ d⟪y, μ x⟫` on the domain of `T`.
- `SelfAdjointSpectralTheorem` : a spectral measure weakly resolving a self-adjoint operator.
- `spectralSquareMomentDomain` : the vectors with finite second moment.
- `DomainAwareSelfAdjointSpectralTheorem` : a spectral measure resolving a self-adjoint operator
  together with its domain.
- `DomainAwareSelfAdjointSpectralTheorem.expUnitaryGroup` : the strongly continuous unitary
  group attached to the spectral measure.

## iii. Table of contents

- A. Essential self-adjointness and closure
  - A.1. Spectral resolutions with domain

## iv. References

* None.

-/

@[expose] public section

noncomputable section

namespace ProbabilisticTheory

open scoped Topology InnerProductSpace Function
open MeasureTheory Set

namespace QuantumMechanics

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ## A. Essential self-adjointness and closure

An operator is essentially self-adjoint when its closure is self-adjoint.
-/

/-- The analytic input needed before applying the unbounded spectral theorem. -/
structure SelfAdjointClosureData
    (T : H →ₗ.[ℂ] H) where
  essentiallySelfAdjoint : LinearPMap.IsEssentiallySelfAdjoint T

namespace SelfAdjointClosureData

variable {T : H →ₗ.[ℂ] H} (D : SelfAdjointClosureData T)

include D

/-- Essential self-adjointness makes the canonical closure self-adjoint. -/
lemma closure_isSelfAdjoint : IsSelfAdjoint T.closure :=
  D.essentiallySelfAdjoint

/-- In particular, the canonical closure is closed. -/
lemma closure_isClosed : T.closure.IsClosed :=
  D.closure_isSelfAdjoint.isClosed

omit [CompleteSpace H] D in
/-- The core operator is contained in its canonical self-adjoint closure. -/
lemma le_closure : T ≤ T.closure :=
  T.le_closure

/-- The canonical closure is the unique self-adjoint extension of the core. -/
lemma unique_selfAdjoint_extension {S : H →ₗ.[ℂ] H}
    (hTS : T ≤ S) (hS : IsSelfAdjoint S) : S = T.closure :=
  LinearPMap.IsEssentiallySelfAdjoint.unique_self_adjoint_extension
    D.essentiallySelfAdjoint hTS hS

omit D in
/-- Build closure data from the von Neumann defect-number criterion. -/
lemma ofDefectNumberEqZero
    (hT : T.IsSymmetric)
    (hdense : T.HasDenseDomain)
    (hpos : T.defectNumber Complex.I = 0)
    (hneg : T.defectNumber (-Complex.I) = 0) :
    SelfAdjointClosureData T :=
  ⟨hT.isEssentiallySelfAdjoint_of_defectNumber_eq_zero hdense hpos hneg⟩

omit D in
/-- Package the reusable defect-index certificate as closure data. -/
lemma ofDefectIndexCertificate {T : H →ₗ.[ℂ] H}
    (C : DefectIndexCertificate T) : SelfAdjointClosureData T :=
  ⟨C.essentiallySelfAdjoint⟩

end SelfAdjointClosureData

/-- The spectral measure `μ` resolves `T`: for `x` in the domain of `T` the identity is integrable
against every `⟪y, μ x⟫`, and `⟪y, T x⟫ = ∫ λ d⟪y, μ x⟫`. -/
def IsWeakSpectralResolution
    (T : H →ₗ.[ℂ] H)
    (μS : WOTSpectralMeasure ℝ H) : Prop :=
  ∀ x : T.domain,
    (∀ y : H, (μS.scalarMeasure (x : H) y).Integrable id) ∧
      ∀ y : H, ⟪y, T x⟫_ℂ = μS.weakIntegral id (x : H) y

/-- The self-adjoint operator is reconstructed from its spectral measure in the weak sense.
The integrability clause is essential: the identity function is generally unbounded, so this
cannot be replaced by the bounded PVM axioms alone. -/
structure SelfAdjointSpectralTheorem
    (T : H →ₗ.[ℂ] H)
    (μS : WOTSpectralMeasure ℝ H) where
  isSelfAdjoint : IsSelfAdjoint T
  reconstruction : IsWeakSpectralResolution T μS

/-!
### A.1. Spectral resolutions with domain

A spectral resolution only describes the operator on its domain. Equality of unbounded operators
also needs the domain to be the set of vectors of finite second moment.
-/

/-- The vectors of finite second moment, `∫ λ² dμₓ < ∞`. -/
def spectralSquareMomentDomain
    (μS : WOTSpectralMeasure ℝ H) : Set H :=
  {x | Integrable (fun (r : ℝ) ↦ r ^ 2) (μS.diagonalMeasure x)}

lemma mem_spectralSquareMomentDomain_iff
    (μS : WOTSpectralMeasure ℝ H) (x : H) :
    x ∈ spectralSquareMomentDomain μS ↔
      Integrable (fun (r : ℝ) ↦ r ^ 2) (μS.diagonalMeasure x) :=
  Iff.rfl

/-- The spectral measure is supported in `[-C, C]`: it vanishes on every measurable set disjoint
from it. -/
def HasBoundedSpectralSupport
    (μS : WOTSpectralMeasure ℝ H) (C : ℝ) : Prop :=
  0 ≤ C ∧ ∀ S : Set ℝ, MeasurableSet S → Disjoint S (Set.Icc (-C) C) → μS S = 0

lemma spectralSquareMomentDomain_eq_univ_of_boundedSupport
    (μS : WOTSpectralMeasure ℝ H) {C : ℝ}
    (hC : HasBoundedSpectralSupport μS C) :
    spectralSquareMomentDomain μS = Set.univ := by
  ext x
  constructor
  · intro _
    trivial
  · intro _
    rw [mem_spectralSquareMomentDomain_iff]
    have hK : MeasurableSet (Set.Icc (-C) C) := measurableSet_Icc
    have hKc : MeasurableSet (Set.Icc (-C) C)ᶜ := hK.compl
    have hμKc : μS (Set.Icc (-C) C)ᶜ = 0 :=
    hC.2 _ hKc disjoint_compl_left
    have hdiagKc : μS.diagonalMeasure x (Set.Icc (-C) C)ᶜ = 0 := by
      rw [μS.diagonalMeasure_apply x _ hKc, hμKc]
      simp
    have hK_ae : ∀ᵐ r ∂μS.diagonalMeasure x, r ∈ Set.Icc (-C) C := by
      rw [ae_iff]
      have hset : {r : ℝ | r ∉ Set.Icc (-C) C} = (Set.Icc (-C) C)ᶜ := by
        rfl
      rw [hset]
      exact hdiagKc
    apply Integrable.of_bound (by fun_prop) (C ^ 2)
    filter_upwards [hK_ae] with r hr
    change |r ^ 2| ≤ C ^ 2
    rw [abs_of_nonneg (sq_nonneg r)]
    exact sq_le_sq' hr.1 hr.2

/-- A spectral measure resolving the self-adjoint operator `T`, whose domain is the set of vectors
of finite second moment. -/
structure DomainAwareSelfAdjointSpectralTheorem
    (T : H →ₗ.[ℂ] H)
    (μS : WOTSpectralMeasure ℝ H)
    extends SelfAdjointSpectralTheorem T μS where
  domain_eq_squareMoment : T.domain = spectralSquareMomentDomain μS

namespace DomainAwareSelfAdjointSpectralTheorem

variable {T : H →ₗ.[ℂ] H}
variable {μS : WOTSpectralMeasure ℝ H}

/-- A spectral measure with bounded support that resolves `T` resolves it together with its domain.
-/
lemma ofBoundedSupport (D : SelfAdjointSpectralTheorem T μS)
    (hdom : (T.domain : Set H) = Set.univ) {C : ℝ}
    (hC : HasBoundedSpectralSupport μS C) :
    DomainAwareSelfAdjointSpectralTheorem T μS where
  toSelfAdjointSpectralTheorem := D
  domain_eq_squareMoment :=
    hdom.trans (spectralSquareMomentDomain_eq_univ_of_boundedSupport μS hC).symm

/-- The self-adjointness part of a domain-aware spectral theorem. -/
lemma isSelfAdjoint_of (D : DomainAwareSelfAdjointSpectralTheorem T μS) :
    IsSelfAdjoint T :=
  D.toSelfAdjointSpectralTheorem.isSelfAdjoint

/-- The weak reconstruction part of a domain-aware spectral theorem. -/
lemma reconstruction_of (D : DomainAwareSelfAdjointSpectralTheorem T μS) :
    IsWeakSpectralResolution T μS :=
  D.toSelfAdjointSpectralTheorem.reconstruction

/-- The domain is exactly the vectors with finite second spectral moment. -/
lemma mem_domain_iff (D : DomainAwareSelfAdjointSpectralTheorem T μS) (x : H) :
    x ∈ T.domain ↔ x ∈ spectralSquareMomentDomain μS := by
  change x ∈ (T.domain : Set H) ↔ x ∈ spectralSquareMomentDomain μS
  rw [D.domain_eq_squareMoment]

/-- The strongly continuous unitary group attached to a domain-aware spectral theorem. Its strong
Stone generator and exact generator domain are the remaining content of Stone's theorem's converse
direction. -/
noncomputable def expUnitaryGroup
    (_D : DomainAwareSelfAdjointSpectralTheorem T μS) :
    WOTSpectralMeasure.StrongUnitaryOneParameterGroup H :=
  QuantumMechanics.WOTSpectralMeasure.expUnitaryGroup μS

lemma expUnitaryGroup_zero (D : DomainAwareSelfAdjointSpectralTheorem T μS) :
    D.expUnitaryGroup 0 = 1 := by
  exact WOTSpectralMeasure.StrongUnitaryOneParameterGroup.zero _

lemma expUnitaryGroup_add (D : DomainAwareSelfAdjointSpectralTheorem T μS) (t s : ℝ) :
    D.expUnitaryGroup (t + s) = D.expUnitaryGroup t * D.expUnitaryGroup s := by
  exact WOTSpectralMeasure.StrongUnitaryOneParameterGroup.add _ t s

lemma expUnitaryGroup_continuous_apply
    (D : DomainAwareSelfAdjointSpectralTheorem T μS) (x : H) :
    Continuous (fun t => D.expUnitaryGroup t x) := by
  exact WOTSpectralMeasure.StrongUnitaryOneParameterGroup.continuous_apply _ x

end DomainAwareSelfAdjointSpectralTheorem

namespace SelfAdjointSpectralTheorem

variable {T : H →ₗ.[ℂ] H} {μS : WOTSpectralMeasure ℝ H}

/-- Transport an unbounded spectral theorem through a Hilbert-space unitary. This is the
representation-level engine: once the theorem is proved for a multiplication model, this
constructor gives it for every unitarily equivalent self-adjoint operator. -/
lemma unitaryConj {H' : Type*} [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
    [CompleteSpace H'] (D : SelfAdjointSpectralTheorem T μS) (u : H ≃ₗᵢ[ℂ] H') :
    SelfAdjointSpectralTheorem (LinearPMap.unitaryConj u T)
      (WOTSpectralMeasure.unitaryConjSpectralMeasure u μS) where
  isSelfAdjoint := LinearPMap.unitaryConj_isSelfAdjoint u D.isSelfAdjoint
  reconstruction := by
    intro x
    let x' : T.domain :=
      ⟨u.symm (x : H'), (LinearPMap.mem_unitaryConj_domain_iff u T).mp x.2⟩
    refine ⟨?_, ?_⟩
    · intro y
      rw [WOTSpectralMeasure.unitaryConjSpectralMeasure_scalarMeasure]
      exact (D.reconstruction x').1 (u.symm y)
    · intro y
      have h := (D.reconstruction x').2 (u.symm y)
      calc
        ⟪y, LinearPMap.unitaryConj u T x⟫_ℂ = ⟪u.symm y, T x'⟫_ℂ := by
          rw [LinearPMap.unitaryConj_apply]
          exact (u.symm.inner_map_eq_flip _ _).symm
        _ = μS.weakIntegral id (x' : H) (u.symm y) := h
        _ = (WOTSpectralMeasure.unitaryConjSpectralMeasure u μS).weakIntegral
            id (x : H') y := by
          symm
          exact WOTSpectralMeasure.unitaryConjSpectralMeasure_weakIntegral
            u μS id x y

end SelfAdjointSpectralTheorem

namespace DomainAwareSelfAdjointSpectralTheorem

variable {T : H →ₗ.[ℂ] H}
variable {μS : WOTSpectralMeasure ℝ H}

/-- Transport the domain-aware theorem through a Hilbert-space unitary. The only additional input
beyond the weak transport is the diagonal-measure equivariance lemma, which makes the
square-moment domain equivariant as well. -/
lemma unitaryConj {H' : Type*} [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
    [CompleteSpace H'] (D : DomainAwareSelfAdjointSpectralTheorem T μS)
    (u : H ≃ₗᵢ[ℂ] H') :
    DomainAwareSelfAdjointSpectralTheorem (LinearPMap.unitaryConj u T)
      (WOTSpectralMeasure.unitaryConjSpectralMeasure u μS) where
  toSelfAdjointSpectralTheorem := D.toSelfAdjointSpectralTheorem.unitaryConj u
  domain_eq_squareMoment := by
    ext x
    change x ∈ (LinearPMap.unitaryConj u T).domain ↔
      x ∈ spectralSquareMomentDomain
        (WOTSpectralMeasure.unitaryConjSpectralMeasure u μS)
    rw [LinearPMap.mem_unitaryConj_domain_iff]
    change u.symm x ∈ T.domain ↔
      Integrable (fun r : ℝ ↦ r ^ 2)
        ((WOTSpectralMeasure.unitaryConjSpectralMeasure u μS).diagonalMeasure x)
    rw [WOTSpectralMeasure.unitaryConjSpectralMeasure_diagonalMeasure]
    exact D.mem_domain_iff (u.symm x)

end DomainAwareSelfAdjointSpectralTheorem

end QuantumMechanics

end ProbabilisticTheory

end
