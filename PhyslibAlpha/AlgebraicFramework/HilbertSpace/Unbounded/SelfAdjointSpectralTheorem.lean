/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.AlgebraicFramework.HilbertSpace.Unbounded.RealAnalytic
public import PhyslibAlpha.AlgebraicFramework.HilbertSpace.Unbounded.StoneUnitaryGroup
public import PhyslibAlpha.AlgebraicFramework.HilbertSpace.Unbounded.WeakIntegral

/-!

# The operator-to-spectrum interface

This is a purely Hilbert-space-level treatment: it deliberately omits the algebra-parametrized
layer (`ConcreteAffiliatedObservable`, `RepresentedAffiliatedObservable`, `AffiliationBridge`,
`FaithfulAffiliationBridge`, and the `SelfAdjointSpectralData`/`EssentialSelfAdjointSpectralData`
endpoint), which is out of scope for this development.

## Essential self-adjointness and closure

For a core operator `T`, essential self-adjointness is precisely the assertion that the canonical
graph closure `T.closure` is self-adjoint. Keeping this as a small data structure
(`SelfAdjointClosureData`) gives concrete constructions (the oscillator, multiplication operators,
and later Schrödinger operators) one common entry point without smuggling a spectral measure into
the definition.

## The domain-aware boundary

`SelfAdjointSpectralTheorem` deliberately records only the weak identity-integral law
(`IsWeakSpectralResolution`). That law is enough for matrix-element reconstruction on the given
domain, but it does not say which vectors belong to the domain. The latter is the square-moment
condition (`spectralSquareMomentDomain`) and must be stated separately before an equality of
unbounded operators can be claimed; `DomainAwareSelfAdjointSpectralTheorem` records both.

## Main definitions

- `SelfAdjointClosureData` : essential self-adjointness of a core, and the uniqueness of its
  self-adjoint closure.
- `IsWeakSpectralResolution` : the weak matrix-element reconstruction law `⟪y, T x⟫ = ∫ λ dμS`.
- `SelfAdjointSpectralTheorem` : self-adjointness plus weak reconstruction against a spectral
  measure, and its transport `unitaryConj` along a Hilbert-space unitary.
- `DomainAwareSelfAdjointSpectralTheorem` : the same, plus the exact domain identification with
  the square-moment domain of the spectral measure; exposes the generated
  `expUnitaryGroup : StrongUnitaryOneParameterGroup H`.

-/

@[expose] public section

noncomputable section

open scoped Topology InnerProductSpace Function
open MeasureTheory Set

namespace QuantumMechanics

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ## Essential self-adjointness and closure

The closure is not an extra choice. For a core operator `T`, essential self-adjointness is
precisely the assertion that the canonical graph closure `T.closure` is self-adjoint. Keeping
this as a small data structure gives concrete constructions (the oscillator, multiplication
operators, and later Schrödinger operators) one common entry point without smuggling a spectral
measure into the definition.
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
@[nolint unusedArguments]
lemma le_closure : T ≤ T.closure :=
  T.le_closure

/-- The canonical closure is the unique self-adjoint extension of the core. -/
lemma unique_selfAdjoint_extension {S : H →ₗ.[ℂ] H}
    (hTS : T ≤ S) (hS : IsSelfAdjoint S) : S = T.closure :=
  LinearPMap.IsEssentiallySelfAdjoint.unique_self_adjoint_extension
    D.essentiallySelfAdjoint hTS hS

omit D in
/-- Build closure data from the von Neumann defect-number criterion. -/
theorem ofDefectNumberEqZero
    (hT : T.IsSymmetric)
    (hdense : T.HasDenseDomain)
    (hpos : T.defectNumber Complex.I = 0)
    (hneg : T.defectNumber (-Complex.I) = 0) :
    SelfAdjointClosureData T :=
  ⟨hT.isEssentiallySelfAdjoint_of_defectNumber_eq_zero hdense hpos hneg⟩

omit D in
/-- Package the reusable defect-index certificate as closure data. -/
theorem ofDefectIndexCertificate {T : H →ₗ.[ℂ] H}
    (C : DefectIndexCertificate T) : SelfAdjointClosureData T :=
  ⟨C.essentiallySelfAdjoint⟩

end SelfAdjointClosureData

/-- The data a concrete unbounded spectral theorem must provide for a self-adjoint `LinearPMap`.
This is an interface, not an axiom hidden in an example: the operator, essential
self-adjointness, and its weak-operator spectral measure are explicit fields. Construction
theorems (multiplication, oscillator, Schrödinger operators) can implement this interface
independently and then reuse all affiliated-observable lemmas. -/
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
### The domain-aware boundary

`SelfAdjointSpectralTheorem` deliberately records only the weak identity-integral law. That law
is enough for matrix-element reconstruction on the given domain, but it does not say which
vectors belong to the domain. The latter is the square-moment condition and must be stated
separately before we can claim an equality of unbounded operators.
-/

/-- The square-moment domain associated to a real weak spectral measure.

For a projection-valued measure this is the usual condition
`∫ λ² d⟪x, E(λ)x⟫ < ∞`. It is expressed using the positive diagonal measure, rather than the
variation of a complex off-diagonal scalar measure; this is the measure that controls the actual
graph norm of the unbounded operator. -/
def spectralSquareMomentDomain
    (μS : WOTSpectralMeasure ℝ H) : Set H :=
  {x | Integrable (fun (r : ℝ) ↦ r ^ 2) (μS.diagonalMeasure x)}

lemma mem_spectralSquareMomentDomain_iff
    (μS : WOTSpectralMeasure ℝ H) (x : H) :
    x ∈ spectralSquareMomentDomain μS ↔
      Integrable (fun (r : ℝ) ↦ r ^ 2) (μS.diagonalMeasure x) :=
  Iff.rfl

/-- A boundedly supported spectral measure has no domain restriction: every vector has a finite
second spectral moment. This is the domain half of the bounded/unbounded interface and is useful
even before a spectral measure has been identified with an operator. -/
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

/-- A domain-aware concrete spectral theorem.

This is the interface required by measurable functional calculus: in addition to
self-adjointness and weak reconstruction, it identifies the operator domain with the
square-moment domain of the PVM. The Cayley spectral-data theorem and the maximal-integral
uniqueness theorem construct this package for every self-adjoint `LinearPMap`; model-specific
work remains only for proving self-adjointness of a smaller core and identifying its closure. -/
structure DomainAwareSelfAdjointSpectralTheorem
    (T : H →ₗ.[ℂ] H)
    (μS : WOTSpectralMeasure ℝ H)
    extends SelfAdjointSpectralTheorem T μS where
  domain_eq_squareMoment : T.domain = spectralSquareMomentDomain μS

namespace DomainAwareSelfAdjointSpectralTheorem

variable {T : H →ₗ.[ℂ] H}
variable {μS : WOTSpectralMeasure ℝ H}

/-- A bounded self-adjoint realization automatically has the maximal square-moment domain when
its spectral measure is boundedly supported. -/
theorem ofBoundedSupport (D : SelfAdjointSpectralTheorem T μS)
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
@[nolint unusedArguments]
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
theorem unitaryConj {H' : Type*} [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
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
theorem unitaryConj {H' : Type*} [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
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

end
