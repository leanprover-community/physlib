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

# The spectral theorem for self-adjoint operators

The statement that a spectral measure on `ℝ` resolves an unbounded self-adjoint operator.

## i. Overview

In quantum mechanics observables such as position, momentum and the Hamiltonian are self-adjoint
operators, and most of them are unbounded, so they are only defined on a dense domain of the
Hilbert space. The spectral theorem says that such an operator is the integral of the identity
function against a projection-valued measure on `ℝ`, its spectral measure. For a normalized state,
the diagonal of this measure is the probability distribution of the outcomes of measuring the
observable in that state; this is the Born rule for observables with arbitrary spectrum.

This file only *states* the spectral theorem, as two structures; the proof that every self-adjoint
operator has such a spectral measure is `unboundedSpectralTheorem` in
`PhyslibAlpha.ProbabilisticTheory.HilbertSpace.Unbounded.CayleySpectralData.SpecTheorem`.
The statement comes in two strengths:

- `SelfAdjointSpectralTheorem` asks for the matrix elements of the operator to be the integrals
  of the identity against the spectral measure, for vectors in the domain of the operator. This
  determines the action of the operator on its domain, but not the domain itself: it does not
  exclude that the operator is a proper restriction of the integral.
- `DomainAwareSelfAdjointSpectralTheorem` asks in addition that the domain is the set of vectors
  whose spectral distribution has finite second moment. Physically, these are the states in which
  the observable has finite variance. This pins the operator down completely, and it is the form
  of the theorem needed to build the unitary group of Stone's theorem, `expUnitaryGroup`, whose
  generator is studied in `PhyslibAlpha.ProbabilisticTheory.HilbertSpace.Unbounded.Flow.Stone`.
  When the operator is a Hamiltonian `H`, the time evolution `exp(-i t H / ħ)` of the system is
  this unitary group at time `-t / ħ`.

Both statements are transported through unitary equivalences, so that once the theorem is known
for a model operator, such as a multiplication operator, it holds for every unitarily equivalent
operator.

In practice an observable is often first written down on a convenient dense domain, for example
smooth rapidly decreasing wave functions, where it is only symmetric. The last section records
`SelfAdjointClosureData`, the statement that such an operator is essentially self-adjoint. Its
closure is then the unique self-adjoint extension, so the observable, and through the spectral
theorem its probability distributions and dynamics, are unambiguous.

## ii. Key results

- `IsWeakSpectralResolution` : the matrix elements of an operator are the integrals of the
  identity against a spectral measure.
- `SelfAdjointSpectralTheorem` : a spectral measure weakly resolving a self-adjoint operator.
- `spectralSquareMomentDomain` : the vectors with finite second spectral moment.
- `DomainAwareSelfAdjointSpectralTheorem` : a spectral measure resolving a self-adjoint operator
  together with its domain.
- `DomainAwareSelfAdjointSpectralTheorem.expUnitaryGroup` : the strongly continuous unitary
  group attached to the spectral measure.
- `SelfAdjointClosureData` : an operator with self-adjoint closure.
- `SelfAdjointClosureData.unique_selfAdjoint_extension` : the self-adjoint extension is unique.

## iii. Table of contents

- A. Weak spectral resolutions
  - A.1. Unitary transport of weak spectral resolutions
- B. The square-moment domain
- C. Spectral resolutions with domain
  - C.1. Bounded spectral support
  - C.2. Unitary transport of spectral resolutions with domain
  - C.3. The unitary group
- D. Essential self-adjointness and closure

## iv. References

- M. Reed and B. Simon, *Methods of Modern Mathematical Physics I: Functional Analysis*,
  Academic Press (1980), Chapter VIII.
- B. C. Hall, *Quantum Theory for Mathematicians*, Springer (2013), Chapters 9 and 10.

-/

@[expose] public section

noncomputable section

namespace ProbabilisticTheory

open scoped Topology InnerProductSpace Function
open MeasureTheory Set

namespace QuantumMechanics

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-!

## A. Weak spectral resolutions

A spectral measure resolves an operator weakly when every matrix element of the operator, between a
vector in its domain and an arbitrary vector, is the integral of the identity function against the
corresponding complex spectral measure.

-/

/-- The spectral measure weakly resolves the operator. That is, for every vector `x` in the domain
of the operator `T` and every vector `y`, the identity function is integrable against the complex
measure `⟪y, μS(·) x⟫` built from the spectral measure `μS`, and the matrix element `⟪y, T x⟫` is
its integral. The integrability clause is needed because the identity function is unbounded. -/
def IsWeakSpectralResolution
    (T : H →ₗ.[ℂ] H)
    (μS : WOTSpectralMeasure ℝ H) : Prop :=
  ∀ x : T.domain,
    (∀ y : H, (μS.scalarMeasure (x : H) y).Integrable id) ∧
      ∀ y : H, ⟪y, T x⟫_ℂ = μS.weakIntegral id (x : H) y

/-- The spectral theorem for a self-adjoint operator, in its weak form: the operator is
self-adjoint and is weakly resolved by the spectral measure. This fixes the action of the operator
on its domain but not the domain itself; see `DomainAwareSelfAdjointSpectralTheorem` for the form
which also fixes the domain. -/
structure SelfAdjointSpectralTheorem
    (T : H →ₗ.[ℂ] H)
    (μS : WOTSpectralMeasure ℝ H) where
  /-- The operator is self-adjoint. -/
  isSelfAdjoint : IsSelfAdjoint T
  /-- The spectral measure weakly resolves the operator. -/
  reconstruction : IsWeakSpectralResolution T μS

namespace SelfAdjointSpectralTheorem

variable {T : H →ₗ.[ℂ] H} {μS : WOTSpectralMeasure ℝ H}

/-!

### A.1. Unitary transport of weak spectral resolutions

-/

/-- Transport the weak spectral theorem through a unitary map between Hilbert spaces. Once the
theorem is proved for a model operator, such as a multiplication operator, this gives it for every
unitarily equivalent self-adjoint operator. -/
lemma unitaryConj {H' : Type*} [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
    [CompleteSpace H'] (D : SelfAdjointSpectralTheorem T μS) (u : H ≃ₗᵢ[ℂ] H') :
    SelfAdjointSpectralTheorem (LinearPMap.unitaryConj u T)
      (WOTSpectralMeasure.unitaryConjSpectralMeasure u μS) where
  isSelfAdjoint := LinearPMap.unitaryConj_isSelfAdjoint u D.isSelfAdjoint
  reconstruction := by
    intro x
    -- the vector of the original Hilbert space corresponding to `x`
    let x' : T.domain :=
      ⟨u.symm (x : H'), (LinearPMap.mem_unitaryConj_domain_iff u T).mp x.2⟩
    refine ⟨?_, ?_⟩
    · intro y
      rw [WOTSpectralMeasure.unitaryConjSpectralMeasure_scalarMeasure]
      exact (D.reconstruction x').1 (u.symm y)
    · intro y
      calc
        ⟪y, LinearPMap.unitaryConj u T x⟫_ℂ = ⟪u.symm y, T x'⟫_ℂ := by
          rw [LinearPMap.unitaryConj_apply]
          exact (u.symm.inner_map_eq_flip _ _).symm
        _ = μS.weakIntegral id (x' : H) (u.symm y) := (D.reconstruction x').2 (u.symm y)
        _ = (WOTSpectralMeasure.unitaryConjSpectralMeasure u μS).weakIntegral
            id (x : H') y :=
          (WOTSpectralMeasure.unitaryConjSpectralMeasure_weakIntegral u μS id x y).symm

end SelfAdjointSpectralTheorem

/-!

## B. The square-moment domain

The domain of the integral of the identity against a spectral measure consists of the vectors whose
spectral distribution has finite second moment. For a normalized state, this is the condition that
the observable has finite variance in that state.

-/

/-- The vectors of finite second spectral moment: those vectors whose diagonal spectral measure
integrates `λ ↦ λ²`. -/
def spectralSquareMomentDomain
    (μS : WOTSpectralMeasure ℝ H) : Set H :=
  {x | Integrable (fun (r : ℝ) ↦ r ^ 2) (μS.diagonalMeasure x)}

/-- A vector lies in the square-moment domain exactly when its diagonal spectral measure integrates
`λ ↦ λ²`. -/
lemma mem_spectralSquareMomentDomain_iff
    (μS : WOTSpectralMeasure ℝ H) (x : H) :
    x ∈ spectralSquareMomentDomain μS ↔
      Integrable (fun (r : ℝ) ↦ r ^ 2) (μS.diagonalMeasure x) :=
  Iff.rfl

/-- The spectral measure is supported in the interval `[-C, C]`, where `C` is a non-negative real
number: it vanishes on every measurable set disjoint from that interval. Physically, every
measurement of the observable then gives an outcome of size at most `C`. -/
def HasBoundedSpectralSupport
    (μS : WOTSpectralMeasure ℝ H) (C : ℝ) : Prop :=
  0 ≤ C ∧ ∀ S : Set ℝ, MeasurableSet S → Disjoint S (Set.Icc (-C) C) → μS S = 0

/-- A spectral measure with bounded support has finite second moment on every vector. -/
lemma spectralSquareMomentDomain_eq_univ_of_boundedSupport
    (μS : WOTSpectralMeasure ℝ H) {C : ℝ} (hC : HasBoundedSpectralSupport μS C) :
    spectralSquareMomentDomain μS = Set.univ := by
  refine Set.eq_univ_of_forall fun x => ?_
  rw [mem_spectralSquareMomentDomain_iff]
  have hKc : MeasurableSet (Set.Icc (-C) C)ᶜ := measurableSet_Icc.compl
  -- the diagonal measure gives no weight to the complement of `[-C, C]`
  have hK_ae : ∀ᵐ r ∂μS.diagonalMeasure x, r ∈ Set.Icc (-C) C := by
    rw [ae_iff]
    change μS.diagonalMeasure x (Set.Icc (-C) C)ᶜ = 0
    rw [μS.diagonalMeasure_apply x _ hKc, hC.2 _ hKc disjoint_compl_left]
    simp
  -- so `λ²` is almost everywhere bounded by `C²`
  apply Integrable.of_bound (by fun_prop) (C ^ 2)
  filter_upwards [hK_ae] with r hr
  change |r ^ 2| ≤ C ^ 2
  rw [abs_of_nonneg (sq_nonneg r)]
  exact sq_le_sq' hr.1 hr.2

/-!

## C. Spectral resolutions with domain

-/

/-- The spectral theorem for a self-adjoint operator, including its domain: the spectral measure
weakly resolves the self-adjoint operator, and the domain of the operator is the set of vectors of
finite second spectral moment. Unlike `SelfAdjointSpectralTheorem`, this determines the operator
completely from its spectral measure. -/
structure DomainAwareSelfAdjointSpectralTheorem
    (T : H →ₗ.[ℂ] H)
    (μS : WOTSpectralMeasure ℝ H)
    extends SelfAdjointSpectralTheorem T μS where
  /-- The domain of the operator is the set of vectors of finite second spectral moment. -/
  domain_eq_squareMoment : T.domain = spectralSquareMomentDomain μS

namespace DomainAwareSelfAdjointSpectralTheorem

variable {T : H →ₗ.[ℂ] H} {μS : WOTSpectralMeasure ℝ H}

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

/-!

### C.1. Bounded spectral support

For an everywhere-defined operator with bounded spectral support the domain condition is automatic.

-/

/-- A spectral measure with bounded support that resolves an everywhere-defined operator resolves
it together with its domain. -/
lemma ofBoundedSupport (D : SelfAdjointSpectralTheorem T μS)
    (hdom : (T.domain : Set H) = Set.univ) {C : ℝ}
    (hC : HasBoundedSpectralSupport μS C) :
    DomainAwareSelfAdjointSpectralTheorem T μS where
  toSelfAdjointSpectralTheorem := D
  domain_eq_squareMoment :=
    hdom.trans (spectralSquareMomentDomain_eq_univ_of_boundedSupport μS hC).symm

/-!

### C.2. Unitary transport of spectral resolutions with domain

-/

/-- Transport the domain-aware spectral theorem through a unitary map between Hilbert spaces. The
only input beyond `SelfAdjointSpectralTheorem.unitaryConj` is that the diagonal spectral measures
are carried along by the unitary, which makes the square-moment domain transform in the same way
as the domain of the operator. -/
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

/-!

### C.3. The unitary group

The spectral measure exponentiates to the strongly continuous one-parameter unitary group
`t ↦ exp(i t T)`. When the operator is a Hamiltonian `H`, the time evolution `exp(-i t H / ħ)` of
the system is this group at time `-t / ħ`.

-/

/-- The strongly continuous unitary group `t ↦ exp(i t T)` obtained by integrating `λ ↦ exp(i t λ)`
against the spectral measure. That the operator is its generator, with the right domain, is the
content of Stone's theorem, developed in
`PhyslibAlpha.ProbabilisticTheory.HilbertSpace.Unbounded.Flow.Stone`. -/
noncomputable def expUnitaryGroup
    (_D : DomainAwareSelfAdjointSpectralTheorem T μS) :
    WOTSpectralMeasure.StrongUnitaryOneParameterGroup H :=
  QuantumMechanics.WOTSpectralMeasure.expUnitaryGroup μS

/-- At time zero the unitary group is the identity. -/
lemma expUnitaryGroup_zero (D : DomainAwareSelfAdjointSpectralTheorem T μS) :
    D.expUnitaryGroup 0 = 1 :=
  WOTSpectralMeasure.StrongUnitaryOneParameterGroup.zero _

/-- The unitary group is a group homomorphism from `ℝ`. -/
lemma expUnitaryGroup_add (D : DomainAwareSelfAdjointSpectralTheorem T μS) (t s : ℝ) :
    D.expUnitaryGroup (t + s) = D.expUnitaryGroup t * D.expUnitaryGroup s :=
  WOTSpectralMeasure.StrongUnitaryOneParameterGroup.add _ t s

/-- The orbit of each vector under the unitary group is continuous in time. -/
lemma expUnitaryGroup_continuous_apply
    (D : DomainAwareSelfAdjointSpectralTheorem T μS) (x : H) :
    Continuous (fun t => D.expUnitaryGroup t x) :=
  WOTSpectralMeasure.StrongUnitaryOneParameterGroup.continuous_apply _ x

end DomainAwareSelfAdjointSpectralTheorem

/-!

## D. Essential self-adjointness and closure

An operator is essentially self-adjoint when its closure is self-adjoint. The spectral theorem then
applies to the closure, which is the unique self-adjoint extension of the operator.

-/

/-- The statement that an operator is essentially self-adjoint, i.e. that its closure is
self-adjoint. Observables are often first written down on a convenient dense domain where they are
only symmetric; this guarantees that such an operator determines a unique self-adjoint observable,
its closure, to which the spectral theorem applies. -/
structure SelfAdjointClosureData
    (T : H →ₗ.[ℂ] H) where
  /-- The operator is essentially self-adjoint. -/
  essentiallySelfAdjoint : LinearPMap.IsEssentiallySelfAdjoint T

namespace SelfAdjointClosureData

variable {T : H →ₗ.[ℂ] H}

/-- The closure of an essentially self-adjoint operator is self-adjoint. -/
lemma closure_isSelfAdjoint (D : SelfAdjointClosureData T) : IsSelfAdjoint T.closure :=
  D.essentiallySelfAdjoint

/-- The closure of an essentially self-adjoint operator is closed. -/
lemma closure_isClosed (D : SelfAdjointClosureData T) : T.closure.IsClosed :=
  D.closure_isSelfAdjoint.isClosed

/-- The closure is the unique self-adjoint extension of an essentially self-adjoint operator. -/
lemma unique_selfAdjoint_extension (D : SelfAdjointClosureData T) {S : H →ₗ.[ℂ] H}
    (hTS : T ≤ S) (hS : IsSelfAdjoint S) : S = T.closure :=
  LinearPMap.IsEssentiallySelfAdjoint.unique_self_adjoint_extension
    D.essentiallySelfAdjoint hTS hS

/-- Von Neumann's criterion: a densely defined symmetric operator whose deficiency numbers at `± i`
both vanish is essentially self-adjoint. -/
lemma ofDefectNumberEqZero (hT : T.IsSymmetric) (hdense : T.HasDenseDomain)
    (hpos : T.defectNumber Complex.I = 0) (hneg : T.defectNumber (-Complex.I) = 0) :
    SelfAdjointClosureData T :=
  ⟨hT.isEssentiallySelfAdjoint_of_defectNumber_eq_zero hdense hpos hneg⟩

/-- An operator with a defect-index certificate is essentially self-adjoint. -/
lemma ofDefectIndexCertificate (C : DefectIndexCertificate T) : SelfAdjointClosureData T :=
  ⟨C.essentiallySelfAdjoint⟩

end SelfAdjointClosureData

end QuantumMechanics

end ProbabilisticTheory

end
