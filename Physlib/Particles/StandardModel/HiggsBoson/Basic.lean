/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.GaugeGroup.Unbroken
public import Mathlib.RepresentationTheory.Stabilizer
public import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
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
- `stabilizer_ofReal`: The stability group of the Higgs vacuum `(0, √a)`, i.e. the gauge
  group left unbroken by it, is `SU(3) × U(1)_EM`.

## iii. Table of contents

- A. The Higgs vector space
  - A.1. Definition of the Higgs vector space
  - A.2. Orthonormal basis
  - A.3. Generating Higgs vectors from real numbers
  - A.4. Action of the gauge group on `HiggsVec`
    - A.4.1. Definition of the representation
    - A.4.2. Unitary nature of the action
    - A.4.3. Group properties of the representation applied to vectors
  - A.5. The Gauge orbit of a Higgs vector
    - A.5.1. The rotation matrix to ofReal
    - A.5.2. Members of orbits
  - A.6. The stability group of a Higgs vector
  - A.7. The electromagnetic U(1) and the phase of the first component
  - A.8. To real scalars
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

* The particle data group has properties of the Higgs boson Review of Particle Physics, PDG.
  [ref: ParticleDataGroup:2018ovx]
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

### A.2. Orthonormal basis

We define an orthonormal basis of `HiggsVec`.

-/

/-- An orthonormal basis of `HiggsVec`. -/
def orthonormBasis : OrthonormalBasis (Fin 2) ℂ HiggsVec :=
  EuclideanSpace.basisFun (Fin 2) ℂ

/-!

### A.3. Generating Higgs vectors from real numbers

Given a real number `a` we define the Higgs vector corresponding to that real number
as `(0, √a)`. This has the property that its norm-squared is equal to `a`.
Following the textbook convention, the non-zero entry sits in the second (lower) component,
which is the electrically neutral component of the Higgs doublet
(see `GaugeGroupI.electromagnetismU1`).

-/

/-- Generating a Higgs vector `(0, √a)` from a real number `a`, such that the norm-squared of
  that Higgs vector is `a`. -/
def ofReal (a : ℝ) : HiggsVec :=
  !₂[0, Real.sqrt a]

@[simp]
lemma ofReal_normSq {a : ℝ} (ha : 0 ≤ a) : ‖ofReal a‖ ^ 2 = a := by
  simp [ofReal, PiLp.norm_sq_eq_of_L2, Real.sq_sqrt ha]

/-!

### A.4. Action of the gauge group on `HiggsVec`

The gauge group of the Standard Model acts on `HiggsVec` by matrix multiplication.

-/

/-!

#### A.4.1. Definition of the representation

-/

/-- The representation of the gauge group `GaugeGroupI` on `HiggsVec`: the `SU(2)`
  factor acts by matrix multiplication, and the `U(1)` factor by scalar
  multiplication with its third power. Hypercharges are normalised as `6Y`, so the
  power `3` corresponds to the textbook hypercharge `Y = 1/2`. -/
def repGaugeGroupI : Representation ℂ GaugeGroupI HiggsVec where
  toFun g :=
    { toFun φ := WithLp.toLp 2 <| g.toU1 ^ 3 • (g.toSU2.1 *ᵥ φ.ofLp)
      map_add' φ ψ := by simp [mulVec_add, smul_add]
      map_smul' c φ := by simp [mulVec_smul, smul_comm c] }
  map_one' := by
    ext φ
    simp
  map_mul' g₁ g₂ := by
    ext φ
    simp [Module.End.mul_apply, smul_smul, mulVec_mulVec, mul_pow, mul_comm]

TODO "When the hypercharge coupling `g′` is introduced, fix its normalisation relative to the
  integer charges `6Y` used here (e.g. the power `3` in `repGaugeGroupI`), so that it agrees with
  the textbook coupling `g′` for the hypercharges `Y`."

lemma repGaugeGroupI_apply (g : StandardModel.GaugeGroupI) (φ : HiggsVec) :
    repGaugeGroupI g φ = (WithLp.toLp 2 <| g.toU1 ^ 3 • (g.toSU2.1 *ᵥ φ.ofLp)) := rfl

lemma repGaugeGroupI_apply_eq_U1_mul_SU2 (g : StandardModel.GaugeGroupI) (φ : HiggsVec) :
    repGaugeGroupI g φ = (WithLp.toLp 2 <| g.toSU2.1 *ᵥ (g.toU1 ^ 3 • φ.ofLp)) := by
  rw [repGaugeGroupI_apply, ← mulVec_smul]

lemma repGaugeGroupI_apply_eq_U1_smul_SU2 (g : StandardModel.GaugeGroupI) (φ : HiggsVec) :
    repGaugeGroupI g φ = (WithLp.toLp 2 <| (g.toU1 ^ 3 • g.toSU2.1) *ᵥ φ.ofLp) := by
  rw [repGaugeGroupI_apply]
  rw [Matrix.smul_mulVec]

/-!

#### A.4.2. Unitary nature of the action

The action of `StandardModel.GaugeGroupI` on `HiggsVec` is unitary.

-/
open InnerProductSpace

@[simp]
lemma repGaugeGroupI_inner (g : StandardModel.GaugeGroupI) (φ ψ : HiggsVec) :
    ⟪repGaugeGroupI g φ, repGaugeGroupI g ψ⟫_ℂ = ⟪φ, ψ⟫_ℂ := by
  rw [repGaugeGroupI_apply, repGaugeGroupI_apply, EuclideanSpace.inner_toLp_toLp,
    EuclideanSpace.inner_eq_star_dotProduct, Submonoid.smul_def, Submonoid.smul_def, star_smul,
    smul_dotProduct, dotProduct_smul, smul_smul, Unitary.mul_star_self_of_mem (g.toU1 ^ 3).2,
    one_smul, star_mulVec, dotProduct_comm, dotProduct_mulVec, vecMul_vecMul,
    ← star_eq_conjTranspose, mem_unitaryGroup_iff'.mp g.toSU2.2.1, vecMul_one, dotProduct_comm]

@[simp]
lemma repGaugeGroupI_norm (g : StandardModel.GaugeGroupI) (φ : HiggsVec) :
    ‖repGaugeGroupI g φ‖ = ‖φ‖ := by
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ), repGaugeGroupI_inner]

/-!

#### A.4.3. Group properties of the representation applied to vectors

-/

lemma repGaugeGroupI_mul_apply (g₁ g₂ : StandardModel.GaugeGroupI) (φ : HiggsVec) :
    repGaugeGroupI (g₁ * g₂) φ = repGaugeGroupI g₁ (repGaugeGroupI g₂ φ) := by
  rw [map_mul, Module.End.mul_apply]

lemma repGaugeGroupI_inv_apply_eq_iff (g : StandardModel.GaugeGroupI) (φ ψ : HiggsVec) :
    repGaugeGroupI g⁻¹ φ = ψ ↔ φ = repGaugeGroupI g ψ := by
  constructor
  · rintro rfl
    rw [Representation.self_inv_apply]
  · rintro rfl
    rw [Representation.inv_self_apply]

/-!

### A.5. The Gauge orbit of a Higgs vector

We show that two Higgs vectors are in the same gauge orbit if and only if they have the same norm.

-/

/-!

#### A.5.1. The rotation matrix to ofReal

We define an element of `GaugeGroupI` which takes a given Higgs vector to the
corresponding `ofReal` Higgs vector.

-/

/-- Given a Higgs vector, a rotation matrix which puts the first component of the
  vector to zero, and the second component to a non-negative real. -/
def toRealGroupElem (φ : HiggsVec) : GaugeGroupI :=
  if hφ : φ = 0 then 1 else by
  have h0' : (‖φ‖ ^ 2 : ℂ) = φ 0 * (starRingEnd ℂ) (φ 0) + φ 1 * (starRingEnd ℂ) (φ 1) := by
    rw [← ofReal_pow, ← @real_inner_self_eq_norm_sq]
    simp only [Fin.isValue, mul_conj, PiLp.inner_apply, Complex.inner, ofReal_re,
      Fin.sum_univ_two, ofReal_add]
  refine ⟨1, ⟨!![φ 1 / ‖φ‖, -φ 0 / ‖φ‖; conj (φ 0) / ‖φ‖, conj (φ 1) / ‖φ‖;], ?_, ?_⟩, 1⟩
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
  /- Determinant equals one. -/
  · have h1 : (‖φ‖ : ℂ) ≠ 0 := ofReal_inj.mp.mt (norm_ne_zero_iff.mpr hφ)
    simp [det_fin_two]
    field_simp
    rw [← ofReal_pow, ← @real_inner_self_eq_norm_sq,]
    simp only [Fin.isValue, mul_conj, PiLp.inner_apply, Complex.inner, ofReal_re,
      Fin.sum_univ_two, ofReal_add]
    rw [← mul_conj, ← mul_conj]
    ring

lemma toRealGroupElem_apply_self (φ : HiggsVec) :
    repGaugeGroupI (toRealGroupElem φ) φ = ofReal (‖φ‖ ^ 2) := by
  by_cases hφ : φ = 0
  · ext i
    fin_cases i <;> simp [hφ, toRealGroupElem, ofReal]
  rw [repGaugeGroupI_apply]
  have h0' : (‖φ‖ ^ 2 : ℂ) = φ 0 * (starRingEnd ℂ) (φ 0) + φ 1 * (starRingEnd ℂ) (φ 1) := by
    rw [← ofReal_pow, ← @real_inner_self_eq_norm_sq]
    simp only [Fin.isValue, mul_conj, PiLp.inner_apply, Complex.inner, ofReal_re,
      Fin.sum_univ_two, ofReal_add]
  have hn : Complex.ofReal ‖φ‖ ≠ 0 := ofReal_inj.mp.mt (norm_ne_zero_iff.mpr hφ)
  simp [toRealGroupElem, hφ, GaugeGroupI.toU1, GaugeGroupI.toSU2]
  ext i
  fin_cases i
  · simp [ofReal, vecHead, vecTail]
    field_simp
    ring
  · simp [ofReal, vecHead, vecTail]
    field_simp
    rw [h0']
    ring

/-!

#### A.5.2. Members of orbits

Members of the orbit of a Higgs vector under the action of `GaugeGroupI` are exactly those
Higgs vectors with the same norm.

-/

/-- Two Higgs vectors are in the same gauge orbit (i.e. related by `repGaugeGroupI`)
  if and only if they have the same norm. -/
lemma exists_repGaugeGroupI_eq_iff_norm_eq (φ : HiggsVec) (ψ : HiggsVec) :
    (∃ g : GaugeGroupI, repGaugeGroupI g φ = ψ) ↔ ‖ψ‖ = ‖φ‖ := by
  constructor
  · rintro ⟨g, rfl⟩
    simp
  · intro h
    use (toRealGroupElem ψ)⁻¹ * toRealGroupElem (φ)
    rw [map_mul, Module.End.mul_apply, toRealGroupElem_apply_self φ, ← h,
      ← toRealGroupElem_apply_self ψ, ← Module.End.mul_apply, ← map_mul,
      inv_mul_cancel, map_one, Module.End.one_apply]

/-!

### A.6. The stability group of a Higgs vector

The stability group of a Higgs vector `φ` is the subgroup `repGaugeGroupI.stabilizer φ` of
`GaugeGroupI` fixing `φ`, i.e. the gauge group left unbroken when the Higgs field takes the
value `φ`. For the vacuum `ofReal a = (0, √a)` with `a > 0` it is `SU(3) × U(1)_EM`, and for
any other non-zero Higgs vector it is a conjugate of this subgroup. The subgroup fixing every
Higgs vector is `SU(3) × ℤ₆`.

-/

/-- A gauge transformation fixes the non-zero Higgs vector `ofReal a = (0, √a)` if and only if
  its `SU(2)` part is `diag(u³, ū³)`, where `u` is its `U(1)` part. -/
lemma mem_stabilizer_ofReal_iff {a : ℝ} (ha : 0 < a) (g : GaugeGroupI) :
    g ∈ repGaugeGroupI.stabilizer (ofReal a) ↔
    GaugeGroupI.toSU2 g = GaugeGroupI.diagSU2 (GaugeGroupI.toU1 g ^ 3) := by
  rw [Representation.mem_stabilizer]
  set M := (GaugeGroupI.toSU2 g : Matrix (Fin 2) (Fin 2) ℂ) with hM
  set u := GaugeGroupI.toU1 g ^ 3 with hu
  have hw : (u : ℂ) * conj (u : ℂ) = 1 := u.2.2
  have hw' : conj (u : ℂ) * (u : ℂ) = 1 := u.2.1
  have hs : (Real.sqrt a : ℂ) ≠ 0 := by simp [Real.sqrt_ne_zero'.mpr ha]
  constructor
  · intro h
    have hu0 : (u : ℂ) ≠ 0 := left_ne_zero_of_mul_eq_one hw
    have h01 : M 0 1 = 0 := by
      simpa [repGaugeGroupI_apply, ofReal, Submonoid.smul_def, mulVec, dotProduct,
        Fin.sum_univ_two, ← hM, ← hu, hu0, hs] using congrArg (fun φ : HiggsVec => φ.ofLp 0) h
    have h1 : (u : ℂ) * (M 1 1 * Real.sqrt a) = Real.sqrt a := by
      simpa [repGaugeGroupI_apply, ofReal, Submonoid.smul_def, mulVec, dotProduct,
        Fin.sum_univ_two, ← hM, ← hu] using congrArg (fun φ : HiggsVec => φ.ofLp 1) h
    have h11 : M 1 1 = conj (u : ℂ) := by
      have h1' : (u : ℂ) * M 1 1 = 1 := mul_right_cancel₀ hs (by linear_combination h1)
      rw [← one_mul (M 1 1), ← hw', mul_assoc, h1', mul_one]
    exact GaugeGroupI.eq_diagSU2_of_apply_zero_one_eq_zero h01 h11
  · intro h
    ext i
    fin_cases i
    · simp [repGaugeGroupI_apply, h, ofReal, Submonoid.smul_def, ← hu]
    · have h1 : (u : ℂ) * (Real.sqrt a * conj (u : ℂ)) = Real.sqrt a := by
        linear_combination (Real.sqrt a : ℂ) * hw
      simpa [repGaugeGroupI_apply, h, ofReal, Submonoid.smul_def, ← hu] using h1

/-- The Higgs vacuum breaks electroweak symmetry down to color and electromagnetism: the
  stability group of the non-zero Higgs vector `ofReal a = (0, √a)` is the subgroup
  `SU(3) × U(1)_EM` of `GaugeGroupI`, with elements `(h, diag(u³, ū³), u)`. -/
theorem stabilizer_ofReal {a : ℝ} (ha : 0 < a) :
    repGaugeGroupI.stabilizer (ofReal a) = UnbrokenGaugeGroupI.incl.range := by
  ext g
  rw [mem_stabilizer_ofReal_iff ha, MonoidHom.mem_range]
  constructor
  · intro h
    exact ⟨(GaugeGroupI.toSU3 g, GaugeGroupI.toU1 g), by ext1 <;> simp [h]⟩
  · rintro ⟨p, rfl⟩
    simp

/-- The stability group of any non-zero Higgs vector is conjugate to `SU(3) × U(1)_EM`. -/
lemma exists_stabilizer_eq_conj_unbrokenGaugeGroupI (φ : HiggsVec) (hφ : φ ≠ 0) :
    ∃ g : GaugeGroupI, repGaugeGroupI.stabilizer φ =
      UnbrokenGaugeGroupI.incl.range.map (MulAut.conj g) := by
  refine ⟨(toRealGroupElem φ)⁻¹, ?_⟩
  rw [← stabilizer_ofReal (pow_pos (norm_pos_iff.mpr hφ) 2), ← Representation.stabilizer_conj]
  congr 1
  rw [eq_comm, repGaugeGroupI_inv_apply_eq_iff, toRealGroupElem_apply_self]

/-- The gauge transformations fixing every Higgs vector are those of the form
  `(h, α⁻³ I₂, α)` with `h ∈ SU(3)` arbitrary and `α` a sixth root of unity, i.e. the subgroup
  `SU(3) × ℤ₆` of `GaugeGroupI`. Here `ℤ₆` sits inside `SU(2) × U(1)`: it is the image there of
  the central `ℤ₆` used for `GaugeGroupℤ₆`, whose elements also carry the `SU(3)` part `α² I₃`,
  so this subgroup contains the central `ℤ₆`. -/
lemma mem_iInf_stabilizer_iff (g : GaugeGroupI) :
    g ∈ ⨅ φ, repGaugeGroupI.stabilizer φ ↔
    ∃ α : rootsOfUnity 6 ℂ, GaugeGroupI.toSU2 g = gaugeGroupℤ₆SU2OfRoot α ∧
      GaugeGroupI.toU1 g = gaugeGroupℤ₆UnitaryOfRoot α := by
  simp only [Subgroup.mem_iInf, Representation.mem_stabilizer]
  constructor
  · intro hφ
    have h2 := (mem_stabilizer_ofReal_iff one_pos g).mp (hφ (ofReal 1))
    set w := GaugeGroupI.toU1 g ^ 3 with hw_def
    have hw : (w : ℂ) * conj (w : ℂ) = 1 := w.2.2
    have hw2 : (w : ℂ) ^ 2 = 1 := by
      have := congrArg (fun φ : HiggsVec => φ.ofLp 0) (hφ !₂[1, 0])
      simpa [repGaugeGroupI_apply, h2, Submonoid.smul_def, ← hw_def, sq] using this
    have h6 : (GaugeGroupI.toU1 g : ℂ) ^ 6 = 1 := by
      rw [← hw2]
      simp [hw_def, ← pow_mul]
    have hcw : conj (w : ℂ) = w := by linear_combination (w : ℂ) * hw - conj (w : ℂ) * hw2
    have hu3 : star (GaugeGroupI.toU1 g : ℂ) ^ 3 = w := by
      rw [← hcw, hw_def]
      simp
    refine ⟨rootsOfUnity.mkOfPowEq _ h6, ?_, ?_⟩
    · apply Subtype.ext
      rw [h2, gaugeGroupℤ₆SU2OfRoot_eq_mul_id, GaugeGroupI.diagSU2_coe,
        rootsOfUnity.coe_mkOfPowEq, hu3]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hcw]
    · ext
      simp
  · rintro ⟨α, h2, h1⟩ φ
    have hα : ((α : ℂˣ) : ℂ) * conj ((α : ℂˣ) : ℂ) = 1 := (gaugeGroupℤ₆UnitaryOfRoot α).2.2
    rw [repGaugeGroupI_apply, h2, h1, gaugeGroupℤ₆SU2OfRoot_eq_mul_id]
    ext i
    simp [Submonoid.smul_def, smul_mulVec, ← mul_assoc, ← mul_pow, hα]

/-!

### A.7. The electromagnetic U(1) and the phase of the first component

-/

/-- The electromagnetic `U(1)` acts on a Higgs vector as `diag(u⁶, 1)`: the upper component
  has electric charge `+1` and the lower component is neutral. -/
lemma electromagnetismU1_repGaugeGroupI_apply (g : unitary ℂ) (φ : HiggsVec) :
    repGaugeGroupI (StandardModel.GaugeGroupI.electromagnetismU1 g) φ =
    (WithLp.toLp 2 <| !![g.1 ^ 6, 0; 0, 1] *ᵥ φ.ofLp) := by
  have h : (g : ℂ) * (starRingEnd ℂ) g = 1 := g.2.2
  rw [repGaugeGroupI_apply, GaugeGroupI.electromagnetismU1_toU1,
    GaugeGroupI.electromagnetismU1_toSU2, GaugeGroupI.diagSU2_coe]
  ext i
  fin_cases i
  · simp [Submonoid.smul_def]
    ring
  · simp [Submonoid.smul_def, ← mul_assoc, ← mul_pow, h]

/-- The electromagnetic `U(1)` leaves the Higgs vector `ofReal a = (0, √a)` invariant:
  the Higgs vacuum is electrically neutral, so electromagnetism is unbroken. -/
lemma electromagnetismU1_repGaugeGroupI_ofReal (g : unitary ℂ) (a : ℝ) :
    repGaugeGroupI (StandardModel.GaugeGroupI.electromagnetismU1 g) (ofReal a) = ofReal a := by
  rw [electromagnetismU1_repGaugeGroupI_apply]
  ext i
  fin_cases i <;> simp [ofReal]

/-- There is an element of the electromagnetic `U(1)` making the first (charged) component of a
  Higgs vector real and non-negative. It fixes second components, and so the Higgs vacuum
  `ofReal a`. This is used to gauge-fix two-Higgs-doublet configurations to
  `Φ1 = (0, ‖Φ1‖)`. -/
lemma exists_electromagnetismU1_fst_eq_norm (φ : HiggsVec) :
    ∃ g : unitary ℂ,
      (repGaugeGroupI (StandardModel.GaugeGroupI.electromagnetismU1 g) φ).ofLp 0 = ‖φ.ofLp 0‖ := by
  let θ := arg (φ 0)
  refine ⟨⟨Complex.exp (-I * θ / 6), by
    simp [Unitary.mem_iff, ← Complex.exp_conj, ← Complex.exp_add, Complex.conj_ofNat]
    ring_nf
    simp⟩, ?_⟩
  rw [electromagnetismU1_repGaugeGroupI_apply]
  simp only [Fin.isValue, neg_mul, cons_mulVec, cons_dotProduct, zero_mul,
    dotProduct_of_isEmpty, add_zero, empty_mulVec, cons_val_zero]
  rw [show vecHead φ.ofLp = φ.ofLp 0 from rfl]
  nth_rewrite 1 [← Complex.norm_mul_exp_arg_mul_I (φ.ofLp 0)]
  rw [← Complex.exp_nat_mul, mul_left_comm, ← Complex.exp_add]
  simp [θ]
  ring_nf
  simp

/-!

### A.8. To real scalars

-/

/-- The underlying real values of the Higgs vector. -/
def toRealScalars : HiggsVec →ₗ[ℝ] (Fin 4 → ℝ) where
  toFun x := fun
    | 0 => (x 0).re
    | 1 => (x 0).im
    | 2 => (x 1).re
    | 3 => (x 1).im
  map_add' x y := by
    ext i
    fin_cases i <;> simp
  map_smul' a x := by
    ext i
    fin_cases i <;> simp

lemma toRealScalars_smul_real (a : ℝ) (φ : HiggsVec) :
    toRealScalars (a • φ) = a • toRealScalars φ := map_smul toRealScalars a φ

lemma ofReal_toRealScalars (a : ℝ) :
    toRealScalars (ofReal a) = !₄[0, 0, Real.sqrt a, 0] := by
  funext i
  fin_cases i <;> simp [ofReal, toRealScalars]

lemma ofReal_toRealScalars_norm (φ : HiggsVec) :
    toRealScalars (ofReal (‖φ‖ ^ 2)) = !₄[0, 0, ‖φ‖, 0] := by
  rw [ofReal_toRealScalars, Real.sqrt_sq (norm_nonneg φ)]

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

TODO "Make `HiggsBundle` an associated bundle."

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
    ContMDiff 𝓘(ℝ, SpaceTime) 𝓘(ℝ, HiggsVec) ⊤ φ.toHiggsVec :=
  fun x0 => (Bundle.contMDiffAt_section x0).mp (φ.contMDiff x0)

lemma const_toHiggsVec_apply (φ : HiggsField) (x : SpaceTime) :
    const (φ.toHiggsVec x) x = φ x := rfl

/-!

### C.2. Smoothness properties of components

We prove some smoothness properties of the components of a Higgs field.

-/

@[fun_prop]
lemma contDiff (φ : HiggsField) :
    ContDiff ℝ ⊤ φ :=
  contMDiff_iff_contDiff.mp φ.toHiggsVec_smooth

lemma toVec_smooth (φ : HiggsField) :
    ContMDiff 𝓘(ℝ, SpaceTime) 𝓘(ℝ, EuclideanSpace ℂ (Fin 2)) ⊤ φ :=
  φ.toHiggsVec_smooth

lemma apply_smooth (φ : HiggsField) :
    ∀ i, ContMDiff 𝓘(ℝ, SpaceTime) 𝓘(ℝ, ℂ) ⊤ (fun (x : SpaceTime) => (φ x i)) :=
  fun i => ((contDiff_piLp 2).mp φ.contDiff i).contMDiff

lemma apply_re_smooth (φ : HiggsField) (i : Fin 2) :
    ContMDiff 𝓘(ℝ, SpaceTime) 𝓘(ℝ, ℝ) ⊤ (reCLM ∘ (fun (x : SpaceTime) => (φ x i))) :=
  reCLM.contMDiff.comp (φ.apply_smooth i)

lemma apply_im_smooth (φ : HiggsField) (i : Fin 2) :
    ContMDiff 𝓘(ℝ, SpaceTime) 𝓘(ℝ, ℝ) ⊤ (imCLM ∘ (fun (x : SpaceTime) => (φ x i))) :=
  imCLM.contMDiff.comp (φ.apply_smooth i)

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
  apply Complex.ext <;> simp [inner_apply, PiLp.inner_apply, equivRealProdCLM_symm_apply] <;> ring

/-- Expands the inner product on Higgs fields in terms of complex components of the
  Higgs fields. -/
lemma inner_expand_conj (φ1 φ2 : HiggsField) (x : SpaceTime) :
    ⟪φ1, φ2⟫_(SpaceTime → ℂ) x = conj (φ1 x 0) * φ2 x 0 + conj (φ1 x 1) * φ2 x 1 := by
  simp [inner_apply, PiLp.inner_apply, mul_comm]

/-!

#### C.3.2. Symmetry properties

-/

lemma inner_symm (φ1 φ2 : HiggsField) :
    conj ⟪φ2, φ1⟫_(SpaceTime → ℂ) = ⟪φ1, φ2⟫_(SpaceTime → ℂ) :=
  funext fun x => inner_conj_symm (φ1 x) (φ2 x)

/-!

#### C.3.3. Linearity conditions

-/

lemma inner_add_left (φ1 φ2 φ3 : HiggsField) :
    ⟪φ1 + φ2, φ3⟫_(SpaceTime → ℂ) = ⟪φ1, φ3⟫_(SpaceTime → ℂ) + ⟪φ2, φ3⟫_(SpaceTime → ℂ) :=
  funext fun x => _root_.inner_add_left (φ1 x) (φ2 x) (φ3 x)

lemma inner_add_right (φ1 φ2 φ3 : HiggsField) :
    ⟪φ1, φ2 + φ3⟫_(SpaceTime → ℂ) = ⟪φ1, φ2⟫_(SpaceTime → ℂ) + ⟪φ1, φ3⟫_(SpaceTime → ℂ) :=
  funext fun x => _root_.inner_add_right (φ1 x) (φ2 x) (φ3 x)

@[simp]
lemma inner_zero_left (φ : HiggsField) :
    ⟪0, φ⟫_(SpaceTime → ℂ) = 0 :=
  funext fun x => _root_.inner_zero_left (φ x)

@[simp]
lemma inner_zero_right (φ : HiggsField) :
    ⟪φ, 0⟫_(SpaceTime → ℂ) = 0 :=
  funext fun x => _root_.inner_zero_right (φ x)

lemma inner_neg_left (φ1 φ2 : HiggsField) :
    ⟪-φ1, φ2⟫_(SpaceTime → ℂ) = -⟪φ1, φ2⟫_(SpaceTime → ℂ) :=
  funext fun x => _root_.inner_neg_left (φ1 x) (φ2 x)

lemma inner_neg_right (φ1 φ2 : HiggsField) :
    ⟪φ1, -φ2⟫_(SpaceTime → ℂ) = -⟪φ1, φ2⟫_(SpaceTime → ℂ) :=
  funext fun x => _root_.inner_neg_right (φ1 x) (φ2 x)

/-!

#### C.3.4. Smoothness of the inner product

-/

lemma inner_smooth (φ1 φ2 : HiggsField) : ContMDiff 𝓘(ℝ, SpaceTime) 𝓘(ℝ, ℂ) ⊤
    ⟪φ1, φ2⟫_(SpaceTime → ℂ) :=
  ContDiff.contMDiff <|
    (isBoundedBilinearMap_inner (𝕜 := ℂ)).contDiff.comp (φ1.contDiff.prodMk φ2.contDiff)

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
  simp [inner_apply, inner_self_eq_norm_sq_to_K]

lemma normSq_eq_inner_self_re (φ : HiggsField) (x : SpaceTime) :
    φ.normSq x = (⟪φ, φ⟫_(SpaceTime → ℂ) x).re := by
  rw [inner_self_eq_normSq, Complex.ofReal_re]

/-- The expansion of the norm squared of into components. -/
lemma normSq_expand (φ : HiggsField) :
    φ.normSq = fun x => (conj (φ x 0) * (φ x 0) + conj (φ x 1) * (φ x 1)).re := by
  funext x
  rw [normSq_eq_inner_self_re, inner_expand_conj]

/-!

#### C.4.2. Positivity

-/

lemma normSq_nonneg (φ : HiggsField) (x : SpaceTime) : 0 ≤ ‖φ‖_H^2 x := sq_nonneg _

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
  rw [show φ.normSq = reCLM ∘ ⟪φ, φ⟫_(SpaceTime → ℂ) from funext (normSq_eq_inner_self_re φ)]
  exact reCLM.contMDiff.comp (φ.inner_smooth φ)

/-!

#### C.4.5. Norm-squared of constant Higgs fields

-/

@[simp]
lemma const_normSq (φ : HiggsVec) (x : SpaceTime) :
    ‖const φ‖_H^2 x = ‖φ‖ ^ 2 := by simp

/-!

### C.5. The action of the gauge group on Higgs fields

The results in this section are currently informal.
-/

/-- The action of `gaugeTransformI` on `HiggsField` acting pointwise through
  `HiggsVec.repGaugeGroupI`. -/
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
