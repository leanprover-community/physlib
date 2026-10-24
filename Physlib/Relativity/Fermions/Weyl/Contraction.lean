/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Mathlib.LinearAlgebra.PerfectPairing.Basic
public import Physlib.Relativity.Fermions.Weyl.LeftHanded
public import Physlib.Relativity.Fermions.Weyl.RightHanded
public import Physlib.Relativity.Fermions.Weyl.DualLeftHanded
public import Physlib.Relativity.Fermions.Weyl.DualRightHanded
/-!

# Contraction of Weyl fermions

The `SL(2, ℂ)`-invariant contractions of Weyl fermions with their duals, unique up to scale.

## i. Overview

A left-handed Weyl fermion `ψ^a` and a dual-left-handed Weyl fermion `φ_a` contract to the
number `ψ^a φ_a`, the dot product of their components in the standard bases. It is invariant
under `SL(2, ℂ)` because `M` acts on `ψ` by `M` and on `φ` by `(M⁻¹)ᵀ`. Likewise a right-handed
fermion `ψ^{dot a}`, acted on by the complex conjugate of `M`, contracts with a
dual-right-handed fermion `φ_{dot a}`, acted on by `(M⁻¹)^†`.

## ii. Key results

- `leftDualContraction` : the contraction `ψ^a φ_a`.
- `dualLeftContraction` : the contraction `φ_a ψ^a`.
- `rightDualContraction` : the contraction `ψ^{dot a} φ_{dot a}`.
- `dualRightContraction` : the contraction `φ_{dot a} ψ^{dot a}`.
- `eq_smul_leftDualContraction` : every invariant pairing of left-handed with dual-left-handed
  Weyl fermions is a multiple of `leftDualContraction`; likewise
  `eq_smul_dualLeftContraction`, `eq_smul_rightDualContraction` and
  `eq_smul_dualRightContraction`.

## iii. Table of contents

- A. Contractions of left-handed Weyl fermions
  - A.1. The contraction `ψ^a φ_a`
    - A.1.1. Basic properties
  - A.2. The contraction `φ_a ψ^a`
    - A.2.1. Basic properties
  - A.3. Symmetry
  - A.4. Nondegeneracy
  - A.5. Perfect pairing
  - A.6. Uniqueness up to scale
- B. Contractions of right-handed Weyl fermions
  - B.1. The contraction `ψ^{dot a} φ_{dot a}`
    - B.1.1. Basic properties
  - B.2. The contraction `φ_{dot a} ψ^{dot a}`
    - B.2.1. Basic properties
  - B.3. Symmetry
  - B.4. Nondegeneracy
  - B.5. Perfect pairing
  - B.6. Uniqueness up to scale

## iv. References

* Dreiner, Haber and Martin, Two-component spinor techniques and Feynman rules for quantum
  field theory and supersymmetry, Phys. Rept. 494 (2010) 1-196. [ref: Dreiner:2008tw]

-/

@[expose] public section

namespace Fermion
noncomputable section

open Matrix
open MatrixGroups
open Complex
open TensorProduct

/-!

## A. Contractions of left-handed Weyl fermions

-/

/-!

### A.1. The contraction `ψ^a φ_a`

-/

/-- The bilinear map `(ψ, φ) ↦ ψ^a φ_a` underlying `leftDualContraction`. -/
def leftDualBi : LeftHandedWeyl →ₗ[ℂ] DualLeftHandedWeyl →ₗ[ℂ] ℂ where
  toFun ψ := {
    toFun := fun φ => ψ.toFin2ℂ ⬝ᵥ φ.toFin2ℂ,
    map_add' := by
      intro φ φ'
      simp only [map_add]
      rw [dotProduct_add]
    map_smul' := by
      intro r φ
      simp only [LinearEquiv.map_smul]
      rw [dotProduct_smul]
      rfl}
  map_add' ψ ψ':= by
    refine LinearMap.ext (fun φ => ?_)
    simp only [map_add, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply]
    rw [add_dotProduct]
  map_smul' r ψ := by
    refine LinearMap.ext (fun φ => ?_)
    simp only [LinearEquiv.map_smul, LinearMap.coe_mk, AddHom.coe_mk]
    rw [smul_dotProduct]
    rfl

/-- The contraction `ψ^a φ_a` of a left-handed with a dual-left-handed Weyl fermion, the dot
  product of their components, as an intertwining map to the trivial representation. -/
def leftDualContraction : (LeftHandedWeyl.rep.tprod DualLeftHandedWeyl.rep).IntertwiningMap
    (Representation.trivial ℂ SL(2,ℂ) ℂ) where
  toLinearMap := TensorProduct.lift leftDualBi
  isIntertwining' M := TensorProduct.ext' fun ψ φ => by
    change (M.1 *ᵥ ψ.toFin2ℂ) ⬝ᵥ (M.1⁻¹ᵀ *ᵥ φ.toFin2ℂ) = ψ.toFin2ℂ ⬝ᵥ φ.toFin2ℂ
    rw [dotProduct_mulVec, vecMul_transpose, mulVec_mulVec]
    simp

/-!

#### A.1.1. Basic properties

-/

lemma leftDualContraction_hom_tmul (ψ : LeftHandedWeyl)
    (φ : DualLeftHandedWeyl) :
    leftDualContraction (ψ ⊗ₜ φ) = ψ.toFin2ℂ ⬝ᵥ φ.toFin2ℂ := by
  rfl

lemma leftDualContraction_basis (i j : Fin 2) :
    leftDualContraction (LeftHandedWeyl.basis i ⊗ₜ DualLeftHandedWeyl.basis j) =
      if i.1 = j.1 then (1 : ℂ) else 0 := by
  rw [leftDualContraction_hom_tmul]
  simp only [LeftHandedWeyl.toFin2ℂ_eq_val, LeftHandedWeyl.basis_val,
    DualLeftHandedWeyl.toFin2ℂ_eq_val, DualLeftHandedWeyl.basis_val, dotProduct_single, mul_one]
  rw [Pi.single_apply]
  simp only [Fin.ext_iff]
  refine ite_congr ?h₁ (congrFun rfl) (congrFun rfl)
  exact Eq.propIntro (fun a => id (Eq.symm a)) fun a => id (Eq.symm a)

/-- Contracting with the `j`-th basis vector picks out the `j`-th component of `ψ`. -/
lemma leftDualContraction_tmul_basis (ψ : LeftHandedWeyl) (j : Fin 2) :
    leftDualContraction (ψ ⊗ₜ DualLeftHandedWeyl.basis j) = ψ.val j := by
  rw [leftDualContraction_hom_tmul, DualLeftHandedWeyl.toFin2ℂ_eq_val,
    DualLeftHandedWeyl.basis_val, dotProduct_single, mul_one]
  rfl

/-!

### A.2. The contraction `φ_a ψ^a`

-/

/-- The bilinear map `(φ, ψ) ↦ φ_a ψ^a` underlying `dualLeftContraction`. -/
def dualLeftBi : DualLeftHandedWeyl →ₗ[ℂ] LeftHandedWeyl →ₗ[ℂ] ℂ where
  toFun ψ := {
    toFun := fun φ => ψ.toFin2ℂ ⬝ᵥ φ.toFin2ℂ,
    map_add' := by
      intro φ φ'
      simp only [map_add]
      rw [dotProduct_add]
    map_smul' := by
      intro r φ
      simp only [LinearEquiv.map_smul]
      rw [dotProduct_smul]
      rfl}
  map_add' ψ ψ':= by
    refine LinearMap.ext (fun φ => ?_)
    simp only [map_add, add_dotProduct, vec2_dotProduct, Fin.isValue, LinearMap.coe_mk,
      AddHom.coe_mk, LinearMap.add_apply]
  map_smul' ψ ψ' := by
    refine LinearMap.ext (fun φ => ?_)
    simp only [_root_.map_smul, smul_dotProduct, vec2_dotProduct, Fin.isValue, smul_eq_mul,
      LinearMap.coe_mk, AddHom.coe_mk, RingHom.id_apply, LinearMap.smul_apply]

/-- The contraction `φ_a ψ^a` of a dual-left-handed with a left-handed Weyl fermion, the dot
  product of their components, as an intertwining map to the trivial representation. -/
def dualLeftContraction : (DualLeftHandedWeyl.rep.tprod LeftHandedWeyl.rep).IntertwiningMap
    (Representation.trivial ℂ SL(2,ℂ) ℂ) where
  toLinearMap := TensorProduct.lift dualLeftBi
  isIntertwining' M := TensorProduct.ext' fun φ ψ => by
    change (M.1⁻¹ᵀ *ᵥ φ.toFin2ℂ) ⬝ᵥ (M.1 *ᵥ ψ.toFin2ℂ) = φ.toFin2ℂ ⬝ᵥ ψ.toFin2ℂ
    rw [dotProduct_mulVec, mulVec_transpose, vecMul_vecMul]
    simp

/-!

#### A.2.1. Basic properties

-/

lemma dualLeftContraction_hom_tmul (φ : DualLeftHandedWeyl) (ψ : LeftHandedWeyl) :
    dualLeftContraction (φ ⊗ₜ ψ) = φ.toFin2ℂ ⬝ᵥ ψ.toFin2ℂ := by
  rfl

lemma dualLeftContraction_basis (i j : Fin 2) :
    dualLeftContraction (DualLeftHandedWeyl.basis i ⊗ₜ LeftHandedWeyl.basis j) =
      if i.1 = j.1 then (1 : ℂ) else 0 := by
  rw [dualLeftContraction_hom_tmul]
  simp only [DualLeftHandedWeyl.toFin2ℂ_eq_val, DualLeftHandedWeyl.basis_val,
    LeftHandedWeyl.toFin2ℂ_eq_val, LeftHandedWeyl.basis_val, dotProduct_single, mul_one]
  rw [Pi.single_apply]
  simp only [Fin.ext_iff]
  refine ite_congr ?h₁ (congrFun rfl) (congrFun rfl)
  exact Eq.propIntro (fun a => id (Eq.symm a)) fun a => id (Eq.symm a)

/-!

### A.3. Symmetry

-/

lemma leftDualContraction_tmul_symm (ψ : LeftHandedWeyl) (φ : DualLeftHandedWeyl) :
    leftDualContraction (ψ ⊗ₜ[ℂ] φ) = dualLeftContraction (φ ⊗ₜ[ℂ] ψ) := by
  rw [leftDualContraction_hom_tmul, dualLeftContraction_hom_tmul, dotProduct_comm]

lemma dualLeftContraction_tmul_symm (φ : DualLeftHandedWeyl) (ψ : LeftHandedWeyl) :
    dualLeftContraction (φ ⊗ₜ[ℂ] ψ) = leftDualContraction (ψ ⊗ₜ[ℂ] φ) := by
  rw [leftDualContraction_tmul_symm]

/-!

### A.4. Nondegeneracy

-/

/-- The contraction is nondegenerate: if `ψ^a φ_a = 0` for every `φ` then `ψ = 0`. -/
lemma eq_zero_of_leftDualContraction_tmul_eq_zero (ψ : LeftHandedWeyl)
    (h : ∀ φ, leftDualContraction (ψ ⊗ₜ φ) = 0) : ψ = 0 :=
  LeftHandedWeyl.toFin2ℂEquiv.injective <| funext fun j => by
    rw [map_zero]
    exact (leftDualContraction_tmul_basis ψ j).symm.trans (h _)

/-- The contraction is nondegenerate: if `φ_a ψ^a = 0` for every `ψ` then `φ = 0`. -/
lemma eq_zero_of_dualLeftContraction_tmul_eq_zero (φ : DualLeftHandedWeyl)
    (h : ∀ ψ, dualLeftContraction (φ ⊗ₜ ψ) = 0) : φ = 0 :=
  DualLeftHandedWeyl.toFin2ℂEquiv.injective <| funext fun j => by
    rw [map_zero, Pi.zero_apply, ← h (LeftHandedWeyl.basis j), dualLeftContraction_hom_tmul,
      LeftHandedWeyl.toFin2ℂ_eq_val, LeftHandedWeyl.basis_val, dotProduct_single, mul_one]

/-!

### A.5. Perfect pairing

-/

/-- The pairing `(ψ, φ) ↦ ψ^a φ_a` is perfect. It identifies dual-left-handed Weyl fermions with
  the dual of left-handed Weyl fermions, and vice versa. -/
instance leftDualBi_isPerfPair : leftDualBi.IsPerfPair :=
  .of_injective
    ((injective_iff_map_eq_zero _).2 fun ψ h =>
      eq_zero_of_leftDualContraction_tmul_eq_zero ψ fun φ => LinearMap.congr_fun h φ)
    ((injective_iff_map_eq_zero _).2 fun φ h =>
      eq_zero_of_dualLeftContraction_tmul_eq_zero φ fun ψ => by
        rw [dualLeftContraction_tmul_symm]
        exact LinearMap.congr_fun h ψ)

/-- The pairing `(φ, ψ) ↦ φ_a ψ^a` is perfect. It identifies left-handed Weyl fermions with the
  dual of dual-left-handed Weyl fermions, and vice versa. -/
instance dualLeftBi_isPerfPair : dualLeftBi.IsPerfPair :=
  .of_injective
    ((injective_iff_map_eq_zero _).2 fun φ h =>
      eq_zero_of_dualLeftContraction_tmul_eq_zero φ fun ψ => LinearMap.congr_fun h ψ)
    ((injective_iff_map_eq_zero _).2 fun ψ h =>
      eq_zero_of_leftDualContraction_tmul_eq_zero ψ fun φ => by
        rw [leftDualContraction_tmul_symm]
        exact LinearMap.congr_fun h φ)

/-!

### A.6. Uniqueness up to scale

-/

/-- Every `SL(2,ℂ)`-invariant pairing of left-handed with dual-left-handed Weyl fermions is a
  multiple of `leftDualContraction`. -/
lemma eq_smul_leftDualContraction
    (B : (LeftHandedWeyl.rep.tprod DualLeftHandedWeyl.rep).IntertwiningMap
      (Representation.trivial ℂ SL(2,ℂ) ℂ)) :
    ∃ z : ℂ, B = z • leftDualContraction := by
  have hinv (C : (LeftHandedWeyl.rep.tprod DualLeftHandedWeyl.rep).IntertwiningMap
      (Representation.trivial ℂ SL(2,ℂ) ℂ)) (M : SL(2,ℂ)) (ψ φ) :
      C (LeftHandedWeyl.rep M ψ ⊗ₜ DualLeftHandedWeyl.rep M φ) = C (ψ ⊗ₜ φ) := by
    simpa using Representation.IntertwiningMap.isIntertwining _ _ C M (ψ ⊗ₜ φ)
  obtain ⟨T, hT⟩ : ∃ T : Module.End ℂ LeftHandedWeyl,
      ∀ ψ φ, B (ψ ⊗ₜ φ) = leftDualContraction (T ψ ⊗ₜ φ) :=
    ⟨leftDualBi.toPerfPair.symm.toLinearMap ∘ₗ curry B.toLinearMap, fun ψ φ =>
      (LinearMap.congr_fun
        (leftDualBi.apply_symm_toPerfPair_self (curry B.toLinearMap ψ)) φ).symm⟩
  obtain ⟨μ, hμ⟩ := LeftHandedWeyl.end_eq_smul_id_of_commute_rep (T := T) fun M =>
    LinearMap.ext fun ψ => sub_eq_zero.1 <|
      eq_zero_of_leftDualContraction_tmul_eq_zero _ fun φ => by
        rw [sub_tmul, map_sub, sub_eq_zero, LinearMap.comp_apply, LinearMap.comp_apply, ← hT,
          ← DualLeftHandedWeyl.rep.self_inv_apply M φ, hinv, hT, hinv]
  refine ⟨μ, Representation.IntertwiningMap.ext (TensorProduct.ext' fun ψ φ => ?_)⟩
  change B (ψ ⊗ₜ φ) = μ • leftDualContraction (ψ ⊗ₜ φ)
  rw [hT, hμ, LinearMap.smul_apply, LinearMap.id_apply, ← smul_tmul', map_smul]

/-- Every `SL(2,ℂ)`-invariant pairing of dual-left-handed with left-handed Weyl fermions is a
  multiple of `dualLeftContraction`. -/
lemma eq_smul_dualLeftContraction
    (B : (DualLeftHandedWeyl.rep.tprod LeftHandedWeyl.rep).IntertwiningMap
      (Representation.trivial ℂ SL(2,ℂ) ℂ)) :
    ∃ z : ℂ, B = z • dualLeftContraction := by
  obtain ⟨z, hz⟩ := eq_smul_leftDualContraction
    (B.comp (Representation.TensorProduct.comm _ _).toIntertwiningMap)
  refine ⟨z, Representation.IntertwiningMap.ext (TensorProduct.ext' fun φ ψ => ?_)⟩
  change B (φ ⊗ₜ ψ) = z • dualLeftContraction (φ ⊗ₜ ψ)
  rw [dualLeftContraction_tmul_symm]
  exact congr($hz (ψ ⊗ₜ φ))

/-!

## B. Contractions of right-handed Weyl fermions

-/

/-!

### B.1. The contraction `ψ^{dot a} φ_{dot a}`

-/

/-- The bilinear map `(ψ, φ) ↦ ψ^{dot a} φ_{dot a}` underlying `rightDualContraction`. -/
def rightDualBi : RightHandedWeyl →ₗ[ℂ] DualRightHandedWeyl →ₗ[ℂ] ℂ where
  toFun ψ := {
    toFun := fun φ => ψ.toFin2ℂ ⬝ᵥ φ.toFin2ℂ,
    map_add' := by
      intro φ φ'
      simp only [map_add]
      rw [dotProduct_add]
    map_smul' := by
      intro r φ
      simp only [LinearEquiv.map_smul]
      rw [dotProduct_smul]
      rfl}
  map_add' ψ ψ':= by
    refine LinearMap.ext (fun φ => ?_)
    simp only [map_add, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply]
    rw [add_dotProduct]
  map_smul' r ψ := by
    refine LinearMap.ext (fun φ => ?_)
    simp only [LinearEquiv.map_smul, LinearMap.coe_mk, AddHom.coe_mk]
    rw [smul_dotProduct]
    rfl

/-- The contraction `ψ^{dot a} φ_{dot a}` of a right-handed with a dual-right-handed Weyl
  fermion, the dot product of their components, as an intertwining map to the trivial
  representation. -/
def rightDualContraction : (RightHandedWeyl.rep.tprod DualRightHandedWeyl.rep).IntertwiningMap
    (Representation.trivial ℂ SL(2,ℂ) ℂ) where
  toLinearMap := TensorProduct.lift rightDualBi
  isIntertwining' M := TensorProduct.ext' fun ψ φ => by
    change (M.1.map star *ᵥ ψ.toFin2ℂ) ⬝ᵥ (M.1⁻¹.conjTranspose *ᵥ φ.toFin2ℂ) =
      ψ.toFin2ℂ ⬝ᵥ φ.toFin2ℂ
    have h1 : (M.1)⁻¹ᴴ = ((M.1)⁻¹.map star)ᵀ := by rfl
    rw [dotProduct_mulVec, h1, vecMul_transpose, mulVec_mulVec]
    have h2 : ((M.1)⁻¹.map star * (M.1).map star) = 1 := by
      refine transpose_inj.mp ?_
      rw [transpose_mul]
      change M.1.conjTranspose * (M.1)⁻¹.conjTranspose = 1ᵀ
      rw [← @conjTranspose_mul]
      simp only [SpecialLinearGroup.det_coe, isUnit_iff_ne_zero, ne_eq, one_ne_zero,
        not_false_eq_true, nonsing_inv_mul, conjTranspose_one, transpose_one]
    rw [h2]
    simp only [one_mulVec, vec2_dotProduct, Fin.isValue, RightHandedWeyl.toFin2ℂEquiv_apply,
      DualRightHandedWeyl.toFin2ℂEquiv_apply]

/-!

#### B.1.1. Basic properties

-/

lemma rightDualContraction_hom_tmul (ψ : RightHandedWeyl)
    (φ : DualRightHandedWeyl) :
    rightDualContraction (ψ ⊗ₜ φ) = ψ.toFin2ℂ ⬝ᵥ φ.toFin2ℂ := by
  rfl

lemma rightDualContraction_basis (i j : Fin 2) :
    rightDualContraction (RightHandedWeyl.basis i ⊗ₜ DualRightHandedWeyl.basis j) =
    if i.1 = j.1 then (1 : ℂ) else 0 := by
  rw [rightDualContraction_hom_tmul]
  simp only [RightHandedWeyl.toFin2ℂ_eq_val, RightHandedWeyl.basis_val,
    DualRightHandedWeyl.toFin2ℂ_eq_val, DualRightHandedWeyl.basis_val, dotProduct_single, mul_one]
  rw [Pi.single_apply]
  simp only [Fin.ext_iff]
  refine ite_congr ?h₁ (congrFun rfl) (congrFun rfl)
  exact Eq.propIntro (fun a => id (Eq.symm a)) fun a => id (Eq.symm a)

/-- Contracting with the `j`-th basis vector picks out the `j`-th component. -/
lemma rightDualContraction_tmul_basis (ψ : RightHandedWeyl) (j : Fin 2) :
    rightDualContraction (ψ ⊗ₜ DualRightHandedWeyl.basis j) = ψ.val j := by
  rw [rightDualContraction_hom_tmul, DualRightHandedWeyl.toFin2ℂ_eq_val,
    DualRightHandedWeyl.basis_val, dotProduct_single, mul_one]
  rfl

/-!

### B.2. The contraction `φ_{dot a} ψ^{dot a}`

-/

/-- The bilinear map `(φ, ψ) ↦ φ_{dot a} ψ^{dot a}` underlying `dualRightContraction`. -/
def dualRightBi : DualRightHandedWeyl →ₗ[ℂ] RightHandedWeyl →ₗ[ℂ] ℂ where
  toFun ψ := {
    toFun := fun φ => ψ.toFin2ℂ ⬝ᵥ φ.toFin2ℂ,
    map_add' := by
      intro φ φ'
      simp only [map_add]
      rw [dotProduct_add]
    map_smul' := by
      intro r φ
      simp only [LinearEquiv.map_smul]
      rw [dotProduct_smul]
      rfl}
  map_add' ψ ψ':= by
    refine LinearMap.ext (fun φ => ?_)
    simp only [map_add, add_dotProduct, vec2_dotProduct, Fin.isValue, LinearMap.coe_mk,
      AddHom.coe_mk, LinearMap.add_apply]
  map_smul' ψ ψ' := by
    refine LinearMap.ext (fun φ => ?_)
    simp only [_root_.map_smul, smul_dotProduct, vec2_dotProduct, Fin.isValue, smul_eq_mul,
      LinearMap.coe_mk, AddHom.coe_mk, RingHom.id_apply, LinearMap.smul_apply]

/-- The contraction `φ_{dot a} ψ^{dot a}` of a dual-right-handed with a right-handed Weyl
  fermion, the dot product of their components, as an intertwining map to the trivial
  representation. -/
def dualRightContraction : (DualRightHandedWeyl.rep.tprod RightHandedWeyl.rep).IntertwiningMap
    (Representation.trivial ℂ SL(2,ℂ) ℂ) where
  toLinearMap := TensorProduct.lift dualRightBi
  isIntertwining' M := TensorProduct.ext' fun φ ψ => by
    change (M.1⁻¹.conjTranspose *ᵥ φ.toFin2ℂ) ⬝ᵥ (M.1.map star *ᵥ ψ.toFin2ℂ) =
      φ.toFin2ℂ ⬝ᵥ ψ.toFin2ℂ
    have h1 : (M.1)⁻¹ᴴ = ((M.1)⁻¹.map star)ᵀ := by rfl
    rw [dotProduct_mulVec, h1, mulVec_transpose, vecMul_vecMul]
    have h2 : ((M.1)⁻¹.map star * (M.1).map star) = 1 := by
      refine transpose_inj.mp ?_
      rw [transpose_mul]
      change M.1.conjTranspose * (M.1)⁻¹.conjTranspose = 1ᵀ
      rw [← @conjTranspose_mul]
      simp only [SpecialLinearGroup.det_coe, isUnit_iff_ne_zero, ne_eq, one_ne_zero,
        not_false_eq_true, nonsing_inv_mul, conjTranspose_one, transpose_one]
    rw [h2]
    simp only [vecMul_one, vec2_dotProduct, Fin.isValue, DualRightHandedWeyl.toFin2ℂEquiv_apply,
      RightHandedWeyl.toFin2ℂEquiv_apply]

/-!

#### B.2.1. Basic properties

-/

lemma dualRightContraction_hom_tmul (φ : DualRightHandedWeyl)
    (ψ : RightHandedWeyl) :
    dualRightContraction (φ ⊗ₜ ψ) = φ.toFin2ℂ ⬝ᵥ ψ.toFin2ℂ := by
  rfl

lemma dualRightContraction_basis (i j : Fin 2) :
    dualRightContraction (DualRightHandedWeyl.basis i ⊗ₜ RightHandedWeyl.basis j) =
    if i.1 = j.1 then (1 : ℂ) else 0 := by
  rw [dualRightContraction_hom_tmul]
  simp only [DualRightHandedWeyl.toFin2ℂ_eq_val, DualRightHandedWeyl.basis_val,
    RightHandedWeyl.toFin2ℂ_eq_val, RightHandedWeyl.basis_val, dotProduct_single, mul_one]
  rw [Pi.single_apply]
  simp only [Fin.ext_iff]
  refine ite_congr ?h₁ (congrFun rfl) (congrFun rfl)
  exact Eq.propIntro (fun a => id (Eq.symm a)) fun a => id (Eq.symm a)

/-!

### B.3. Symmetry

-/

lemma rightDualContraction_tmul_symm (ψ : RightHandedWeyl) (φ : DualRightHandedWeyl) :
    rightDualContraction (ψ ⊗ₜ[ℂ] φ) = dualRightContraction (φ ⊗ₜ[ℂ] ψ) := by
  rw [rightDualContraction_hom_tmul, dualRightContraction_hom_tmul, dotProduct_comm]

lemma dualRightContraction_tmul_symm (φ : DualRightHandedWeyl) (ψ : RightHandedWeyl) :
    dualRightContraction (φ ⊗ₜ[ℂ] ψ) = rightDualContraction (ψ ⊗ₜ[ℂ] φ) := by
  rw [rightDualContraction_tmul_symm]

/-!

### B.4. Nondegeneracy

-/

/-- The contraction is nondegenerate: if `ψ^{dot a} φ_{dot a} = 0` for every `φ` then
  `ψ = 0`. -/
lemma eq_zero_of_rightDualContraction_tmul_eq_zero (ψ : RightHandedWeyl)
    (h : ∀ φ, rightDualContraction (ψ ⊗ₜ φ) = 0) : ψ = 0 :=
  RightHandedWeyl.toFin2ℂEquiv.injective <| funext fun j => by
    rw [map_zero]
    exact (rightDualContraction_tmul_basis ψ j).symm.trans (h _)

/-- The contraction is nondegenerate: if `φ_{dot a} ψ^{dot a} = 0` for every `ψ` then
  `φ = 0`. -/
lemma eq_zero_of_dualRightContraction_tmul_eq_zero (φ : DualRightHandedWeyl)
    (h : ∀ ψ, dualRightContraction (φ ⊗ₜ ψ) = 0) : φ = 0 :=
  DualRightHandedWeyl.toFin2ℂEquiv.injective <| funext fun j => by
    rw [map_zero, Pi.zero_apply, ← h (RightHandedWeyl.basis j), dualRightContraction_hom_tmul,
      RightHandedWeyl.toFin2ℂ_eq_val, RightHandedWeyl.basis_val, dotProduct_single, mul_one]

/-!

### B.5. Perfect pairing

-/

/-- The pairing `(ψ, φ) ↦ ψ^{dot a} φ_{dot a}` is perfect. It identifies dual-right-handed Weyl
  fermions with the dual of right-handed Weyl fermions, and vice versa. -/
instance rightDualBi_isPerfPair : rightDualBi.IsPerfPair :=
  .of_injective
    ((injective_iff_map_eq_zero _).2 fun ψ h =>
      eq_zero_of_rightDualContraction_tmul_eq_zero ψ fun φ => LinearMap.congr_fun h φ)
    ((injective_iff_map_eq_zero _).2 fun φ h =>
      eq_zero_of_dualRightContraction_tmul_eq_zero φ fun ψ => by
        rw [dualRightContraction_tmul_symm]
        exact LinearMap.congr_fun h ψ)

/-- The pairing `(φ, ψ) ↦ φ_{dot a} ψ^{dot a}` is perfect. It identifies right-handed Weyl
  fermions with the dual of dual-right-handed Weyl fermions, and vice versa. -/
instance dualRightBi_isPerfPair : dualRightBi.IsPerfPair :=
  .of_injective
    ((injective_iff_map_eq_zero _).2 fun φ h =>
      eq_zero_of_dualRightContraction_tmul_eq_zero φ fun ψ => LinearMap.congr_fun h ψ)
    ((injective_iff_map_eq_zero _).2 fun ψ h =>
      eq_zero_of_rightDualContraction_tmul_eq_zero ψ fun φ => by
        rw [rightDualContraction_tmul_symm]
        exact LinearMap.congr_fun h φ)

/-!

### B.6. Uniqueness up to scale

The argument is that of A.6.

-/

/-- Every `SL(2,ℂ)`-invariant pairing of right-handed with dual-right-handed Weyl fermions is a
  multiple of `rightDualContraction`. -/
lemma eq_smul_rightDualContraction
    (B : (RightHandedWeyl.rep.tprod DualRightHandedWeyl.rep).IntertwiningMap
      (Representation.trivial ℂ SL(2,ℂ) ℂ)) :
    ∃ z : ℂ, B = z • rightDualContraction := by
  have hinv (C : (RightHandedWeyl.rep.tprod DualRightHandedWeyl.rep).IntertwiningMap
      (Representation.trivial ℂ SL(2,ℂ) ℂ)) (M : SL(2,ℂ)) (ψ φ) :
      C (RightHandedWeyl.rep M ψ ⊗ₜ DualRightHandedWeyl.rep M φ) = C (ψ ⊗ₜ φ) := by
    simpa using Representation.IntertwiningMap.isIntertwining _ _ C M (ψ ⊗ₜ φ)
  obtain ⟨T, hT⟩ : ∃ T : Module.End ℂ RightHandedWeyl,
      ∀ ψ φ, B (ψ ⊗ₜ φ) = rightDualContraction (T ψ ⊗ₜ φ) :=
    ⟨rightDualBi.toPerfPair.symm.toLinearMap ∘ₗ curry B.toLinearMap, fun ψ φ =>
      (LinearMap.congr_fun
        (rightDualBi.apply_symm_toPerfPair_self (curry B.toLinearMap ψ)) φ).symm⟩
  obtain ⟨μ, hμ⟩ := RightHandedWeyl.end_eq_smul_id_of_commute_rep (T := T) fun M =>
    LinearMap.ext fun ψ => sub_eq_zero.1 <|
      eq_zero_of_rightDualContraction_tmul_eq_zero _ fun φ => by
        rw [sub_tmul, map_sub, sub_eq_zero, LinearMap.comp_apply, LinearMap.comp_apply, ← hT,
          ← DualRightHandedWeyl.rep.self_inv_apply M φ, hinv, hT, hinv]
  refine ⟨μ, Representation.IntertwiningMap.ext (TensorProduct.ext' fun ψ φ => ?_)⟩
  change B (ψ ⊗ₜ φ) = μ • rightDualContraction (ψ ⊗ₜ φ)
  rw [hT, hμ, LinearMap.smul_apply, LinearMap.id_apply, ← smul_tmul', map_smul]

/-- Every `SL(2,ℂ)`-invariant pairing of dual-right-handed with right-handed Weyl fermions is a
  multiple of `dualRightContraction`. -/
lemma eq_smul_dualRightContraction
    (B : (DualRightHandedWeyl.rep.tprod RightHandedWeyl.rep).IntertwiningMap
      (Representation.trivial ℂ SL(2,ℂ) ℂ)) :
    ∃ z : ℂ, B = z • dualRightContraction := by
  obtain ⟨z, hz⟩ := eq_smul_rightDualContraction
    (B.comp (Representation.TensorProduct.comm _ _).toIntertwiningMap)
  refine ⟨z, Representation.IntertwiningMap.ext (TensorProduct.ext' fun φ ψ => ?_)⟩
  change B (φ ⊗ₜ ψ) = z • dualRightContraction (φ ⊗ₜ ψ)
  rw [dualRightContraction_tmul_symm]
  exact congr($hz (ψ ⊗ₜ φ))

end
end Fermion
