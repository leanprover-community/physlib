/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import PhysLean.Particles.StandardModel.Basic
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
/-!

# The Higgs field

## i. Overview

The Higgs field describes is the underlying field of the Higgs boson.
It is a map from SpaceTime to a 2-dimensional complex vector space.
In this module we define the Higgs field and prove some basic properties.

## ii. Key results

- `HiggsVec`: The 2-dimensional complex vector space which is the target space of the Higgs field.
  This vector space is equipped with an action of the global gauge group of the Standard Model.
- `HiggsBundle`: The trivial vector bundle over `SpaceTime` with fiber `HiggsVec`.
- `HiggsField`: The type of smooth sections of the `HiggsBundle`, i.e., the type of Higgs fields.

## iii. Table of contents

- A. The Higgs vector space
  - A.1. Definition of the Higgs vector space
  - A.2. Relation to `(Fin 2 → ℂ)`
  - A.3. Orthonormal basis
  - A.4. Generating Higgs vectors from real numbers
  - A.5. Action of the gauge group on `HiggsVec`
    - A.5.1. Definition of the action
    - A.5.2. Unitary nature of the action
  - A.6. The Gauge orbit of a Higgs vector
    - A.6.1. The rotation matrix to ofReal
    - A.6.2. Members of orbits
  - A.7. The stability group of a Higgs vector
- B. The Higgs bundle
  - B.1. Definition of the Higgs bundle
  - B.2. Instance of a vector bundle
- C. The Higgs fields
  - C.1. Relations between `HiggsField` and `HiggsVec`
    - C.1.1. The constant Higgs field
    - C.1.2. The map from `HiggsField` to `SpaceTime → HiggsVec`
  - C.2. Smoothness properties of components
  - C.3. The pointwise inner product
    - C.3.1. Basic equalities
    - C.3.2. Symmetry properties
    - C.3.3. Linearity conditions
    - C.3.4. Smoothness of the inner product
  - C.4. The pointwise norm
    - C.4.1. Basic equalities
    - C.4.2. Positivity
    - C.4.3. On the zero section
    - C.4.4. Smoothness of the norm-squared
    - C.4.5. Norm-squared of constant Higgs fields
  - C.5. The action of the gauge group on Higgs fields

## iv. References

- The particle data group has properties of the Higgs boson
  [Review of Particle Physics, PDG][ParticleDataGroup:2018ovx]

-/

@[expose] public section

namespace StandardModel
noncomputable section

open Manifold
open Matrix
open Complex
open ComplexConjugate
open SpaceTime

/-!

## A. The Higgs vector space

The target space of the Higgs field is a 2-dimensional complex vector space.
In this section we will define this vector space, and the action of the
global gauge group on it.

-/

/-!

### A.1. Definition of the Higgs vector space

-/
/-- The vector space `HiggsVec` is defined to be the complex Euclidean space of dimension 2.
  For a given spacetime point a Higgs field gives a value in `HiggsVec`. -/
abbrev HiggsVec := EuclideanSpace ℂ (Fin 2)

namespace HiggsVec

/-!

### A.2. Relation to `(Fin 2 → ℂ)`

We define the continuous linear map from `HiggsVec` to `(Fin 2 → ℂ)` achieved by
casting vectors, we also show that this map is smooth.

-/

/-- The continuous linear map from the vector space `HiggsVec` to `(Fin 2 → ℂ)` achieved by
casting vectors. -/
def toFin2ℂ : HiggsVec →L[ℝ] (Fin 2 → ℂ) where
  toFun x := x
  map_add' x y := rfl
  map_smul' a x := rfl

/-- The map `toFin2ℂ` is smooth. -/
lemma smooth_toFin2ℂ : ContMDiff 𝓘(ℝ, HiggsVec) 𝓘(ℝ, Fin 2 → ℂ) ⊤ toFin2ℂ :=
  ContinuousLinearMap.contMDiff toFin2ℂ

/-!

### A.3. Orthonormal basis

We define an orthonormal basis of `HiggsVec`.

-/

/-- An orthonormal basis of `HiggsVec`. -/
def orthonormBasis : OrthonormalBasis (Fin 2) ℂ HiggsVec :=
  EuclideanSpace.basisFun (Fin 2) ℂ

/-!

### A.4. Generating Higgs vectors from real numbers

Given a real number `a` we define the Higgs vector corresponding to that real number
as `(√a, 0)`. This has the property that it's norm is equal to `a`.

-/

/-- Generating a Higgs vector from a real number, such that the norm-squared of that Higgs vector
  is the given real number. -/
def ofReal (a : ℝ) : HiggsVec :=
  !₂[Real.sqrt a, 0]

@[simp]
lemma ofReal_normSq {a : ℝ} (ha : 0 ≤ a) : ‖ofReal a‖ ^ 2 = a := by
  simp only [ofReal]
  rw [PiLp.norm_sq_eq_of_L2]
  rw [@Fin.sum_univ_two]
  simp only [Fin.isValue, cons_val_zero, norm_real, Real.norm_eq_abs, _root_.sq_abs, cons_val_one,
    norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero]
  exact Real.sq_sqrt ha

/-!

### A.5. Action of the gauge group on `HiggsVec`

The gauge group of the Standard Model acts on `HiggsVec` by matrix multiplication.

-/

/-!

#### A.5.1. Definition of the action

-/

instance : SMul StandardModel.GaugeGroupI HiggsVec where
  smul g φ := WithLp.toLp 2 <| g.toU1 ^ 3 • (g.toSU2.1 *ᵥ φ.ofLp)

lemma gaugeGroupI_smul_eq (g : StandardModel.GaugeGroupI) (φ : HiggsVec) :
    g • φ = (WithLp.toLp 2 <| g.toU1 ^ 3 • (g.toSU2.1 *ᵥ φ.ofLp)) := rfl

lemma gaugeGroupI_smul_eq_U1_mul_SU2 (g : StandardModel.GaugeGroupI) (φ : HiggsVec) :
    g • φ = (WithLp.toLp 2 <| g.toSU2.1 *ᵥ (g.toU1 ^ 3 • φ.ofLp)) := by
  rw [gaugeGroupI_smul_eq, ← mulVec_smul]

lemma gaugeGroupI_smul_eq_U1_smul_SU2 (g : StandardModel.GaugeGroupI) (φ : HiggsVec) :
    g • φ = (WithLp.toLp 2 <| (g.toU1 ^ 3 • g.toSU2.1) *ᵥ φ.ofLp) := by
  rw [gaugeGroupI_smul_eq]
  rw [Matrix.smul_mulVec]

instance : MulAction StandardModel.GaugeGroupI HiggsVec where
  one_smul φ := by simp [gaugeGroupI_smul_eq]
  mul_smul g₁ g₂ φ := by
    rw [gaugeGroupI_smul_eq, gaugeGroupI_smul_eq, gaugeGroupI_smul_eq_U1_mul_SU2]
    rw [mulVec_smul, mulVec_smul, smul_smul, mulVec_mulVec]
    congr
    simp [mul_pow]

instance : DistribMulAction StandardModel.GaugeGroupI HiggsVec where
  smul_zero g := by
    rw [gaugeGroupI_smul_eq_U1_smul_SU2]
    simp
  smul_add g φ ψ := by
    rw [gaugeGroupI_smul_eq_U1_smul_SU2]
    simp [mulVec_add]
    simp [← gaugeGroupI_smul_eq_U1_smul_SU2]
/-!

#### A.5.2. Unitary nature of the action

The action of `StandardModel.GaugeGroupI` on `HiggsVec` is unitary.

-/
open InnerProductSpace

@[simp]
lemma gaugeGroupI_smul_inner (g : StandardModel.GaugeGroupI) (φ ψ : HiggsVec) :
    ⟪g • φ, g • ψ⟫_ℂ = ⟪φ, ψ⟫_ℂ := by
  calc ⟪g • φ, g • ψ⟫_ℂ
    _ = WithLp.ofLp (g • ψ) ⬝ᵥ star (WithLp.ofLp (g • φ)) := by
      rw [EuclideanSpace.inner_eq_star_dotProduct]
    _ = (g.toSU2.1 *ᵥ (g.toU1 ^ 3 • ψ)) ⬝ᵥ star (g.toSU2.1 *ᵥ (g.toU1 ^ 3 • φ)) := by
      rw [gaugeGroupI_smul_eq_U1_mul_SU2, gaugeGroupI_smul_eq_U1_mul_SU2]
    _ = (g.toSU2.1 *ᵥ (g.toU1 ^ 3 • ψ)) ⬝ᵥ (star ((g.toU1 ^ 3 • φ)) ᵥ* star (g.toSU2.1)) := by
      rw [star_mulVec]
      rfl
    _ = ((star (g.toSU2.1) * g.toSU2.1) *ᵥ (g.toU1 ^ 3 • ψ)) ⬝ᵥ star ((g.toU1 ^ 3 • φ)) := by
      rw [dotProduct_comm, ← Matrix.dotProduct_mulVec, dotProduct_comm, mulVec_mulVec]
      rfl
    _ = ((g.toU1 ^ 3 • ψ)) ⬝ᵥ star ((g.toU1 ^ 3 • φ)) := by
      rw [mem_unitaryGroup_iff'.mp (GaugeGroupI.toSU2 g).2.1]
      simp
    _ = ((g.toU1 ^ 3 • ψ)) ⬝ᵥ star (g.toU1 ^ 3) • star (φ.toFin2ℂ) := by
      congr
      ext i
      simp only [Pi.star_apply, RCLike.star_def, star_pow, Pi.smul_apply]
      change (starRingEnd ℂ) (GaugeGroupI.toU1 g ^ 3 * φ i) = _
      simp
      rfl
    _ = (ψ ⬝ᵥ star (φ.toFin2ℂ)) := by
      erw [dotProduct_smul, smul_dotProduct, smul_smul, Unitary.star_mul_self]
      simp

@[simp]
lemma gaugeGroupI_smul_norm (g : StandardModel.GaugeGroupI) (φ : HiggsVec) :
    ‖g • φ‖ = ‖φ‖ := by
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ)]
  rw [gaugeGroupI_smul_inner]

/-!

### A.6. The Gauge orbit of a Higgs vector

We show that two Higgs vectors are in the same gauge orbit if and only if they have the same norm.

-/

/-!

#### A.6.1. The rotation matrix to ofReal

We define an element of `GaugeGroupI` which takes a given Higgs vector to the
corresponding `ofReal` Higgs vector.

-/

/-- Given a Higgs vector, a rotation matrix which puts the second component of the
  vector to zero, and the first component to a real -/
def toRealGroupElem (φ : HiggsVec) : GaugeGroupI :=
  if hφ : φ = 0 then 1 else by
  have h0 : (‖φ‖^2 : ℝ) = φ 0 * (starRingEnd ℂ) (φ 0) + φ 1 * (starRingEnd ℂ) (φ 1) := by
    rw [← @real_inner_self_eq_norm_sq]
    simp only [Fin.isValue, mul_conj, PiLp.inner_apply, Complex.inner, ofReal_re,
      Fin.sum_univ_two, ofReal_add]
  have h0' : (‖φ‖^2 : ℂ) = φ 0 * (starRingEnd ℂ) (φ 0) + φ 1 * (starRingEnd ℂ) (φ 1) := by
    rw [← h0]
    simp
  refine ⟨1, ⟨!![conj (φ 0) / ‖φ‖, conj (φ 1) / ‖φ‖; -φ 1 /‖φ‖, φ 0 /‖φ‖;], ?_, ?_⟩, 1⟩
  /- Member of the unitary group. -/
  · simp only [Fin.isValue, SetLike.mem_coe]
    rw [mem_unitaryGroup_iff']
    funext i j
    rw [Matrix.mul_apply]
    simp only [Fin.isValue, star_apply, of_apply, cons_val', cons_val_fin_one, RCLike.star_def,
      Fin.sum_univ_two, cons_val_zero, cons_val_one]
    have hφ : Complex.ofReal ‖φ‖ ≠ 0 := ofReal_inj.mp.mt (norm_ne_zero_iff.mpr hφ)
    fin_cases i <;> fin_cases j <;>
    all_goals
    · simp
      field_simp
      rw [h0']
      ring
  /- Determinant equals zero. -/
  · have h1 : (‖φ‖ : ℂ) ≠ 0 := ofReal_inj.mp.mt (norm_ne_zero_iff.mpr hφ)
    simp [det_fin_two]
    field_simp
    rw [← ofReal_pow, ← @real_inner_self_eq_norm_sq,]
    simp only [Fin.isValue, mul_conj, PiLp.inner_apply, Complex.inner, ofReal_re,
      Fin.sum_univ_two, ofReal_add]
    rw [← mul_conj, ← mul_conj]
    ring

lemma toRealGroupElem_smul_self (φ : HiggsVec) :
    (toRealGroupElem φ) • φ = ofReal (‖φ‖ ^ 2) := by
  by_cases hφ : φ = 0
  · simp [hφ, toRealGroupElem]
    ext i
    fin_cases i <;> simp [ofReal]
  rw [gaugeGroupI_smul_eq]
  have h0 : (‖φ‖^2 : ℝ) = φ 0 * (starRingEnd ℂ) (φ 0) + φ 1 * (starRingEnd ℂ) (φ 1) := by
    rw [← @real_inner_self_eq_norm_sq]
    simp only [Fin.isValue, mul_conj, PiLp.inner_apply, Complex.inner, ofReal_re,
      Fin.sum_univ_two, ofReal_add]
  have h0' : (‖φ‖^2 : ℂ) = φ 0 * (starRingEnd ℂ) (φ 0) + φ 1 * (starRingEnd ℂ) (φ 1) := by
    rw [← h0]
    simp
  simp [toRealGroupElem, hφ]
  · simp [GaugeGroupI.toU1, GaugeGroupI.toSU2]
    ext i
    have hφ : Complex.ofReal ‖φ‖ ≠ 0 := ofReal_inj.mp.mt (norm_ne_zero_iff.mpr hφ)
    fin_cases i
    · simp [ofReal]
      field_simp
      rw [h0']
      ring_nf
      rfl
    · simp [ofReal]
      field_simp
      change -(φ 1 * φ 0) + φ 0 * φ 1= _
      ring

/-!

#### A.6.2. Members of orbits

Members of the orbit of a Higgs vector under the action of `GaugeGroupI` are exactly those
Higgs vectors with the same norm.

-/

lemma mem_orbit_gaugeGroupI_iff (φ : HiggsVec) (ψ : HiggsVec) :
    ψ ∈ MulAction.orbit GaugeGroupI φ ↔ ‖ψ‖ = ‖φ‖ := by
  constructor
  · intro h
    obtain ⟨g, rfl⟩ := h
    simp
  · intro h
    use (toRealGroupElem ψ)⁻¹ * toRealGroupElem (φ)
    simp only
    rw [← smul_smul, toRealGroupElem_smul_self φ, ← h, ← toRealGroupElem_smul_self ψ, smul_smul]
    simp

/-!

### A.7. The stability group of a Higgs vector

We find the stability group of a Higgs vector, and the stability group of the set of
all Higgs vectors.

The items in this section are marked as `informal_lemma` as they are not yet formalized.

-/

/-- The Higgs boson breaks electroweak symmetry down to the electromagnetic force, i.e., the
stability group of the action of `rep` on `![0, Complex.ofReal ‖φ‖]`, for non-zero `‖φ‖`, is the
`SU(3) × U(1)` subgroup of `gaugeGroup := SU(3) × SU(2) × U(1)` with the embedding given by
`(g, e^{i θ}) ↦ (g, diag (e ^ {3 * i θ}, e ^ {- 3 * i θ}), e^{i θ})`.
-/
informal_lemma stability_group_single where
  deps := [``StandardModel.HiggsVec]
  tag := "6V2MD"

/-- The subgroup of `gaugeGroup := SU(3) × SU(2) × U(1)` which preserves every `HiggsVec` by the
action of `StandardModel.HiggsVec.rep` is given by `SU(3) × ℤ₆` where `ℤ₆` is the subgroup of
`SU(2) × U(1)` with elements `(α^(-3) * I₂, α)` where `α` is a sixth root of unity.
-/
informal_lemma stability_group where
  deps := [``HiggsVec]
  tag := "6V2MO"

/-!

## A.8. Gauge action removing phase from second component

-/

lemma ofU1Subgroup_smul_eq_smul (g : unitary ℂ) (φ : HiggsVec) :
    (StandardModel.GaugeGroupI.ofU1Subgroup g) • φ =
    (WithLp.toLp 2 <| !![1, 0; 0, g.1 ^ 6] *ᵥ φ.ofLp) := by
  rw [gaugeGroupI_smul_eq_U1_smul_SU2]
  simp only [GaugeGroupI.ofU1Subgroup_toU1, GaugeGroupI.ofU1Subgroup_toSU2, SubmonoidClass.coe_pow,
    star_pow, RCLike.star_def, smul_of, smul_cons, smul_zero, smul_empty, cons_mulVec,
    cons_dotProduct, zero_mul, dotProduct_of_isEmpty, add_zero, zero_add, empty_mulVec, one_mul,
    WithLp.toLp.injEq, vecCons_inj, mul_eq_mul_right_iff, and_true]
  apply And.intro
  · have h0 : g ^ 3 • (starRingEnd ℂ) ↑g ^ 3 = 1 := by
      trans (normSq (g ^ 3).1 : ℂ)
      · rw [← mul_conj]
        simp
        rfl
      · rw [normSq_eq_norm_sq]
        simp
    simp [h0]
  · left
    trans (g ^ 3 : ℂ) • (g ^ 3 : ℂ)
    · rfl
    simp only [smul_eq_mul]
    ring

lemma gaugeGroupI_smul_phase_snd (φ : HiggsVec) :
    ∃ g : StandardModel.GaugeGroupI,
      (g • φ).ofLp 1 = ‖(φ.ofLp 1)‖ ∧
      (∀ φ1 : HiggsVec, (g • φ1).ofLp 0 = φ1.ofLp 0) ∧
      (∀ a : ℝ, g • (!₂[a, 0] : HiggsVec) = (!₂[a, 0] : HiggsVec)) := by
  let θ := arg (φ 1)
  use StandardModel.GaugeGroupI.ofU1Subgroup ⟨Complex.exp (-I * θ / 6), by
    rw [Unitary.mem_iff]
    simp [← Complex.exp_conj, ← Complex.exp_add, Complex.conj_ofNat]
    ring_nf
    simp⟩
  apply And.intro
  · rw [ofU1Subgroup_smul_eq_smul]
    simp only [Fin.isValue, neg_mul, cons_mulVec, cons_dotProduct, one_mul, zero_mul,
      dotProduct_of_isEmpty, add_zero, zero_add, empty_mulVec, cons_val_one, cons_val_fin_one]
    trans Complex.exp (-I * θ / 6) ^ 6 * φ.ofLp 1
    · congr
      simp
    have habs : φ.ofLp 1 = cexp (I * arg (φ.ofLp 1)) * ‖φ.ofLp 1‖ := by
      conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I (φ.ofLp 1)]
      ring_nf
    conv_lhs => rw [habs]
    rw [← mul_assoc, ← Complex.exp_nat_mul, ← Complex.exp_add]
    simp [θ]
    ring_nf
    simp
  apply And.intro
  · intro φ
    rw [ofU1Subgroup_smul_eq_smul]
    simp
    rfl
  · intro a
    simp [ofU1Subgroup_smul_eq_smul]
    ext i
    fin_cases i <;> simp

end HiggsVec

/-!

## B. The Higgs bundle

We define the Higgs bundle as the trivial vector bundle with base `SpaceTime` and fiber `HiggsVec`.
The Higgs field will then be defined as smooth sections of this bundle.
-/

/-!

### B.1. Definition of the Higgs bundle

We define the Higgs bundle.

-/

TODO "6V2IS" "Make `HiggsBundle` an associated bundle."

/-- The `HiggsBundle` is defined as the trivial vector bundle with base `SpaceTime` and
  fiber `HiggsVec`. Thus as a manifold it corresponds to `ℝ⁴ × ℂ²`. -/
abbrev HiggsBundle := Bundle.Trivial SpaceTime HiggsVec

/-!

### B.2. Instance of a vector bundle

We given the Higgs bundle an instance of a smooth vector bundle.

-/

/-- The instance of a smooth vector bundle with total space `HiggsBundle` and fiber `HiggsVec`. -/
instance : ContMDiffVectorBundle ⊤ HiggsVec HiggsBundle (Lorentz.Vector.asSmoothManifold 3) :=
  Bundle.Trivial.contMDiffVectorBundle HiggsVec

/-!

## C. The Higgs fields

Higgs fields are smooth sections of the Higgs bundle.
This corresponds to smooth maps from `SpaceTime` to `HiggsVec`.
We here define the type of Higgs fields and create an API around them.

-/

/-- The type `HiggsField` is defined such that elements are smooth sections of the trivial
  vector bundle `HiggsBundle`. Such elements are Higgs fields. Since `HiggsField` is
  trivial as a vector bundle, a Higgs field is equivalent to a smooth map
  from `SpaceTime` to `HiggsVec`. -/
abbrev HiggsField : Type := ContMDiffSection
  (Lorentz.Vector.asSmoothManifold 3) HiggsVec ⊤ HiggsBundle

namespace HiggsField
open HiggsVec

/-!

### C.1. Relations between `HiggsField` and `HiggsVec`

-/

/-!

#### C.1.1. The constant Higgs field

We define the constant Higgs field associated to a given Higgs vector.

-/

/-- Given a vector in `HiggsVec` the constant Higgs field with value equal to that
section. -/
def const : HiggsVec →ₗ[ℝ] HiggsField where
  toFun φ := {
    toFun := fun _ ↦ φ,
    contMDiff_toFun := by
      intro x
      rw [Bundle.contMDiffAt_section]
      exact contMDiffAt_const}
  map_add' φ ψ := by
    ext1 x
    simp
  map_smul' a φ := by
    ext1 x
    simp

/-- For all spacetime points, the constant Higgs field defined by a Higgs vector,
  returns that Higgs Vector. -/
@[simp]
lemma const_apply (φ : HiggsVec) (x : SpaceTime) : const φ x = φ := rfl

/-!

#### C.1.2. The map from `HiggsField` to `SpaceTime → HiggsVec`

-/

/-- Given a `HiggsField`, the corresponding map from `SpaceTime` to `HiggsVec`. -/
def toHiggsVec (φ : HiggsField) : SpaceTime → HiggsVec := φ

lemma toHiggsVec_smooth (φ : HiggsField) :
    ContMDiff 𝓘(ℝ, SpaceTime) 𝓘(ℝ, HiggsVec) ⊤ φ.toHiggsVec := by
  intro x0
  have h1 := φ.contMDiff x0
  rw [Bundle.contMDiffAt_section] at h1
  exact h1

lemma const_toHiggsVec_apply (φ : HiggsField) (x : SpaceTime) :
    const (φ.toHiggsVec x) x = φ x := rfl

lemma toFin2ℂ_comp_toHiggsVec (φ : HiggsField) :
    φ.toHiggsVec = φ := rfl

/-!

### C.2. Smoothness properties of components

We prove some smoothness properties of the components of a Higgs field.

-/

@[fun_prop]
lemma contDiff (φ : HiggsField) :
    ContDiff ℝ ⊤ φ := by
  simpa [contMDiff_iff_contDiff] using φ.toHiggsVec_smooth

lemma toVec_smooth (φ : HiggsField) :
    ContMDiff 𝓘(ℝ, SpaceTime) 𝓘(ℝ, EuclideanSpace ℂ (Fin 2)) ⊤ φ :=
  φ.toHiggsVec_smooth

lemma apply_smooth (φ : HiggsField) :
    ∀ i, ContMDiff 𝓘(ℝ, SpaceTime) 𝓘(ℝ, ℂ) ⊤ (fun (x : SpaceTime) => (φ x i)) := by
  have h1 := φ.contDiff
  intro i
  refine ContDiff.contMDiff ?_
  simp only
  rw [contDiff_piLp] at h1
  exact h1 i

lemma apply_re_smooth (φ : HiggsField) (i : Fin 2) :
    ContMDiff 𝓘(ℝ, SpaceTime) 𝓘(ℝ, ℝ) ⊤ (reCLM ∘ (fun (x : SpaceTime) => (φ x i))) :=
  (ContinuousLinearMap.contMDiff reCLM).comp (φ.apply_smooth i)

lemma apply_im_smooth (φ : HiggsField) (i : Fin 2) :
    ContMDiff 𝓘(ℝ, SpaceTime) 𝓘(ℝ, ℝ) ⊤ (imCLM ∘ (fun (x : SpaceTime) => (φ x i))) :=
  (ContinuousLinearMap.contMDiff imCLM).comp (φ.apply_smooth i)

/-!

### C.3. The pointwise inner product

The pointwise inner product on the Higgs field.

-/

open InnerProductSpace

instance : Inner (SpaceTime → ℂ) (HiggsField) where
  inner φ1 φ2 := fun x => ⟪φ1 x, φ2 x⟫_ℂ

/-!

#### C.3.1. Basic equalities

-/

lemma inner_apply (φ1 φ2 : HiggsField) (x : SpaceTime) :
    ⟪φ1, φ2⟫_(SpaceTime → ℂ) x = ⟪φ1 x, φ2 x⟫_ℂ := rfl

lemma inner_eq_expand (φ1 φ2 : HiggsField) :
    ⟪φ1, φ2⟫_(SpaceTime → ℂ) = fun x => equivRealProdCLM.symm (((φ1 x 0).re * (φ2 x 0).re
    + (φ1 x 1).re * (φ2 x 1).re+ (φ1 x 0).im * (φ2 x 0).im + (φ1 x 1).im * (φ2 x 1).im),
    ((φ1 x 0).re * (φ2 x 0).im + (φ1 x 1).re * (φ2 x 1).im
    - (φ1 x 0).im * (φ2 x 0).re - (φ1 x 1).im * (φ2 x 1).re)) := by
  funext x
  simp only [inner_apply, PiLp.inner_apply, RCLike.inner_apply, Fin.sum_univ_two,
    equivRealProdCLM_symm_apply, ofReal_add, ofReal_mul, ofReal_sub]
  rw [RCLike.conj_eq_re_sub_im, RCLike.conj_eq_re_sub_im]
  nth_rewrite 1 [← RCLike.re_add_im (φ2 x 0)]
  nth_rewrite 1 [← RCLike.re_add_im (φ2 x 1)]
  ring_nf
  simp only [Fin.isValue, RCLike.re_to_complex, coe_algebraMap, RCLike.I_to_complex,
    RCLike.im_to_complex, I_sq, mul_neg, mul_one, neg_mul, sub_neg_eq_add, one_mul]
  ring

/-- Expands the inner product on Higgs fields in terms of complex components of the
  Higgs fields. -/
lemma inner_expand_conj (φ1 φ2 : HiggsField) (x : SpaceTime) :
    ⟪φ1, φ2⟫_(SpaceTime → ℂ) x = conj (φ1 x 0) * φ2 x 0 + conj (φ1 x 1) * φ2 x 1 := by
  simp [inner_apply, PiLp.inner_apply]
  ring

/-!

#### C.3.2. Symmetry properties

-/

lemma inner_symm (φ1 φ2 : HiggsField) :
    conj ⟪φ2, φ1⟫_(SpaceTime → ℂ) = ⟪φ1, φ2⟫_(SpaceTime → ℂ) := by
  funext x
  simp only [inner_apply, Pi.conj_apply, inner_conj_symm]

/-!

#### C.3.3. Linearity conditions

-/

lemma inner_add_left (φ1 φ2 φ3 : HiggsField) :
    ⟪φ1 + φ2, φ3⟫_(SpaceTime → ℂ) = ⟪φ1, φ3⟫_(SpaceTime → ℂ) + ⟪φ2, φ3⟫_(SpaceTime → ℂ) := by
  funext x
  simp [inner_apply]
  rw [_root_.inner_add_left]

lemma inner_add_right (φ1 φ2 φ3 : HiggsField) :
    ⟪φ1, φ2 + φ3⟫_(SpaceTime → ℂ) = ⟪φ1, φ2⟫_(SpaceTime → ℂ) + ⟪φ1, φ3⟫_(SpaceTime → ℂ) := by
  funext x
  simp [inner_apply]
  rw [_root_.inner_add_right]

@[simp]
lemma inner_zero_left (φ : HiggsField) :
    ⟪0, φ⟫_(SpaceTime → ℂ) = 0 := by
  funext x
  simp [inner_apply]

@[simp]
lemma inner_zero_right (φ : HiggsField) :
    ⟪φ, 0⟫_(SpaceTime → ℂ) = 0 := by
  funext x
  simp [inner_apply]

lemma inner_neg_left (φ1 φ2 : HiggsField) :
    ⟪-φ1, φ2⟫_(SpaceTime → ℂ) = -⟪φ1, φ2⟫_(SpaceTime → ℂ) := by
  funext x
  simp [inner_apply]

lemma inner_neg_right (φ1 φ2 : HiggsField) :
    ⟪φ1, -φ2⟫_(SpaceTime → ℂ) = -⟪φ1, φ2⟫_(SpaceTime → ℂ) := by
  funext x
  simp [inner_apply]

/-!

#### C.3.4. Smoothness of the inner product

-/

lemma inner_smooth (φ1 φ2 : HiggsField) : ContMDiff 𝓘(ℝ, SpaceTime) 𝓘(ℝ, ℂ) ⊤
    ⟪φ1, φ2⟫_(SpaceTime → ℂ) := by
  rw [inner_eq_expand]
  exact (ContinuousLinearMap.contMDiff (equivRealProdCLM.symm : ℝ × ℝ →L[ℝ] ℂ)).comp $
    (((((φ1.apply_re_smooth 0).smul (φ2.apply_re_smooth 0)).add
    ((φ1.apply_re_smooth 1).smul (φ2.apply_re_smooth 1))).add
    ((φ1.apply_im_smooth 0).smul (φ2.apply_im_smooth 0))).add
    ((φ1.apply_im_smooth 1).smul (φ2.apply_im_smooth 1))).prodMk_space $
    ((((φ1.apply_re_smooth 0).smul (φ2.apply_im_smooth 0)).add
    ((φ1.apply_re_smooth 1).smul (φ2.apply_im_smooth 1))).sub
    ((φ1.apply_im_smooth 0).smul (φ2.apply_re_smooth 0))).sub
    ((φ1.apply_im_smooth 1).smul (φ2.apply_re_smooth 1))

/-!

### C.4. The pointwise norm

We define the pointwise norm-squared of a Higgs field.

-/

/-- Given an element `φ` of `HiggsField`, `normSq φ` is defined as the
  the function `SpaceTime → ℝ` obtained by taking the square norm of the
  pointwise Higgs vector. In other words, `normSq φ x = ‖φ x‖ ^ 2`.

  The notation `‖φ‖_H^2` is used for the `normSq φ`. -/
@[simp]
def normSq (φ : HiggsField) : SpaceTime → ℝ := fun x => ‖φ x‖ ^ 2

@[inherit_doc normSq]
scoped[StandardModel.HiggsField] notation "‖" φ1 "‖_H^2" => normSq φ1

/-!

#### C.4.1. Basic equalities

-/

lemma inner_self_eq_normSq (φ : HiggsField) (x : SpaceTime) :
    ⟪φ, φ⟫_(SpaceTime → ℂ) x = ‖φ‖_H^2 x := by
  simp only [inner_apply, PiLp.inner_apply, RCLike.inner_apply, Fin.sum_univ_two, Fin.isValue,
    normSq, ofReal_pow]
  rw [← Complex.ofReal_pow, PiLp.norm_sq_eq_of_L2]
  rw [Fin.sum_univ_two, ofReal_add, ofReal_pow]
  rw [mul_comm, conj_mul', mul_comm, conj_mul', ofReal_pow]

lemma normSq_eq_inner_self_re (φ : HiggsField) (x : SpaceTime) :
    φ.normSq x = (⟪φ, φ⟫_(SpaceTime → ℂ) x).re := by
  rw [inner_self_eq_normSq]
  simp only [normSq, ofReal_pow]
  rw [← Complex.ofReal_pow, Complex.ofReal_re]

/-- The expansion of the norm squared of into components. -/
lemma normSq_expand (φ : HiggsField) :
    φ.normSq = fun x => (conj (φ x 0) * (φ x 0) + conj (φ x 1) * (φ x 1)).re := by
  funext x
  rw [normSq_eq_inner_self_re, inner_expand_conj]

/-!

#### C.4.2. Positivity

-/

lemma normSq_nonneg (φ : HiggsField) (x : SpaceTime) : 0 ≤ ‖φ‖_H^2 x := by
  simp [normSq]

/-!

#### C.4.3. On the zero section

-/

@[simp]
lemma normSq_zero : ‖0‖_H^2 = 0 := by
  ext x
  simp

/-!

#### C.4.4. Smoothness of the norm-squared

-/

/-- The norm squared of the Higgs field is a smooth function on space-time. -/
lemma normSq_smooth (φ : HiggsField) : ContMDiff 𝓘(ℝ, SpaceTime) 𝓘(ℝ, ℝ) ⊤ φ.normSq := by
  rw [normSq_expand]
  refine ContMDiff.add ?_ ?_
  · simp only [mul_re, conj_re, conj_im, neg_mul, sub_neg_eq_add]
    exact ((φ.apply_re_smooth 0).smul (φ.apply_re_smooth 0)).add $
      (φ.apply_im_smooth 0).smul (φ.apply_im_smooth 0)
  · simp only [mul_re, conj_re, conj_im, neg_mul, sub_neg_eq_add]
    exact ((φ.apply_re_smooth 1).smul (φ.apply_re_smooth 1)).add $
      (φ.apply_im_smooth 1).smul (φ.apply_im_smooth 1)

/-!

#### C.4.5. Norm-squared of constant Higgs fields

-/

@[simp]
lemma const_normSq (φ : HiggsVec) (x : SpaceTime) :
    ‖const φ‖_H^2 x = ‖φ‖ ^ 2 := by
  simp [normSq, const_apply]

/-!

### C.5. The action of the gauge group on Higgs fields

The results in this section are currently informal.
-/

TODO "6V2MV" "Define the global gauge action on HiggsField."
TODO "6V2M3" "Prove `⟪φ1, φ2⟫_H` invariant under the global gauge action. (norm_map_of_mem_unitary)"
TODO "6V2NA" "Prove invariance of potential under global gauge action."

/-- The action of `gaugeTransformI` on `HiggsField` acting pointwise through `HiggsVec.rep`. -/
informal_definition gaugeAction where
  deps := [``gaugeTransformI]
  tag := "6V2NP"

/-- There exists a `g` in `gaugeTransformI` such that `gaugeAction g φ = φ'` iff
`φ(x)^† φ(x) = φ'(x)^† φ'(x)`.
-/
informal_lemma guage_orbit where
  deps := [``gaugeAction]
  tag := "6V2NX"

/-- For every smooth map `f` from `SpaceTime` to `ℝ` such that `f` is positive semidefinite, there
exists a Higgs field `φ` such that `f = φ^† φ`.
-/
informal_lemma gauge_orbit_surject where
  deps := [``HiggsField, ``SpaceTime]
  tag := "6V2OC"

end HiggsField

end
end StandardModel
