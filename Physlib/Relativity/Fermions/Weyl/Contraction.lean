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

- `LeftHandedWeyl.contr` : the contraction `ψ^a φ_a`.
- `DualLeftHandedWeyl.contr` : the contraction `φ_a ψ^a`.
- `RightHandedWeyl.contr` : the contraction `ψ^{dot a} φ_{dot a}`.
- `DualRightHandedWeyl.contr` : the contraction `φ_{dot a} ψ^{dot a}`.
- `LeftHandedWeyl.eq_smul_contr` : every invariant pairing of left-handed with dual-left-handed
  Weyl fermions is a multiple of `LeftHandedWeyl.contr`; likewise
  `DualLeftHandedWeyl.eq_smul_contr`, `RightHandedWeyl.eq_smul_contr` and
  `DualRightHandedWeyl.eq_smul_contr`.

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

/-- The bilinear map `(ψ, φ) ↦ ψ^a φ_a` underlying `LeftHandedWeyl.contr`. -/
def LeftHandedWeyl.contrBi : LeftHandedWeyl →ₗ[ℂ] DualLeftHandedWeyl →ₗ[ℂ] ℂ where
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
def LeftHandedWeyl.contr : (LeftHandedWeyl.rep.tprod DualLeftHandedWeyl.rep).IntertwiningMap
    (Representation.trivial ℂ SL(2,ℂ) ℂ) where
  toLinearMap := TensorProduct.lift LeftHandedWeyl.contrBi
  isIntertwining' M := TensorProduct.ext' fun ψ φ => by
    change (M.1 *ᵥ ψ.toFin2ℂ) ⬝ᵥ (M.1⁻¹ᵀ *ᵥ φ.toFin2ℂ) = ψ.toFin2ℂ ⬝ᵥ φ.toFin2ℂ
    rw [dotProduct_mulVec, vecMul_transpose, mulVec_mulVec]
    simp

/-!

#### A.1.1. Basic properties

-/

lemma LeftHandedWeyl.contr_tmul (ψ : LeftHandedWeyl)
    (φ : DualLeftHandedWeyl) :
    LeftHandedWeyl.contr (ψ ⊗ₜ φ) = ψ.toFin2ℂ ⬝ᵥ φ.toFin2ℂ := by
  rfl

lemma LeftHandedWeyl.contr_basis (i j : Fin 2) :
    LeftHandedWeyl.contr (LeftHandedWeyl.basis i ⊗ₜ DualLeftHandedWeyl.basis j) =
      if i.1 = j.1 then (1 : ℂ) else 0 := by
  rw [LeftHandedWeyl.contr_tmul]
  simp only [LeftHandedWeyl.toFin2ℂ_eq_val, LeftHandedWeyl.basis_val,
    DualLeftHandedWeyl.toFin2ℂ_eq_val, DualLeftHandedWeyl.basis_val, dotProduct_single, mul_one]
  rw [Pi.single_apply]
  simp only [Fin.ext_iff]
  refine ite_congr ?h₁ (congrFun rfl) (congrFun rfl)
  exact Eq.propIntro (fun a => id (Eq.symm a)) fun a => id (Eq.symm a)

/-- Contracting with the `j`-th basis vector picks out the `j`-th component of `ψ`. -/
lemma LeftHandedWeyl.contr_tmul_basis (ψ : LeftHandedWeyl) (j : Fin 2) :
    LeftHandedWeyl.contr (ψ ⊗ₜ DualLeftHandedWeyl.basis j) = ψ.val j := by
  rw [LeftHandedWeyl.contr_tmul, DualLeftHandedWeyl.toFin2ℂ_eq_val,
    DualLeftHandedWeyl.basis_val, dotProduct_single, mul_one]
  rfl

/-!

### A.2. The contraction `φ_a ψ^a`

-/

/-- The bilinear map `(φ, ψ) ↦ φ_a ψ^a` underlying `DualLeftHandedWeyl.contr`. -/
def DualLeftHandedWeyl.contrBi : DualLeftHandedWeyl →ₗ[ℂ] LeftHandedWeyl →ₗ[ℂ] ℂ where
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
def DualLeftHandedWeyl.contr : (DualLeftHandedWeyl.rep.tprod LeftHandedWeyl.rep).IntertwiningMap
    (Representation.trivial ℂ SL(2,ℂ) ℂ) where
  toLinearMap := TensorProduct.lift DualLeftHandedWeyl.contrBi
  isIntertwining' M := TensorProduct.ext' fun φ ψ => by
    change (M.1⁻¹ᵀ *ᵥ φ.toFin2ℂ) ⬝ᵥ (M.1 *ᵥ ψ.toFin2ℂ) = φ.toFin2ℂ ⬝ᵥ ψ.toFin2ℂ
    rw [dotProduct_mulVec, mulVec_transpose, vecMul_vecMul]
    simp

/-!

#### A.2.1. Basic properties

-/

lemma DualLeftHandedWeyl.contr_tmul (φ : DualLeftHandedWeyl) (ψ : LeftHandedWeyl) :
    DualLeftHandedWeyl.contr (φ ⊗ₜ ψ) = φ.toFin2ℂ ⬝ᵥ ψ.toFin2ℂ := by
  rfl

lemma DualLeftHandedWeyl.contr_basis (i j : Fin 2) :
    DualLeftHandedWeyl.contr (DualLeftHandedWeyl.basis i ⊗ₜ LeftHandedWeyl.basis j) =
      if i.1 = j.1 then (1 : ℂ) else 0 := by
  rw [DualLeftHandedWeyl.contr_tmul]
  simp only [DualLeftHandedWeyl.toFin2ℂ_eq_val, DualLeftHandedWeyl.basis_val,
    LeftHandedWeyl.toFin2ℂ_eq_val, LeftHandedWeyl.basis_val, dotProduct_single, mul_one]
  rw [Pi.single_apply]
  simp only [Fin.ext_iff]
  refine ite_congr ?h₁ (congrFun rfl) (congrFun rfl)
  exact Eq.propIntro (fun a => id (Eq.symm a)) fun a => id (Eq.symm a)

/-!

### A.3. Symmetry

-/

lemma LeftHandedWeyl.contr_tmul_symm (ψ : LeftHandedWeyl) (φ : DualLeftHandedWeyl) :
    LeftHandedWeyl.contr (ψ ⊗ₜ[ℂ] φ) = DualLeftHandedWeyl.contr (φ ⊗ₜ[ℂ] ψ) := by
  rw [LeftHandedWeyl.contr_tmul, DualLeftHandedWeyl.contr_tmul, dotProduct_comm]

lemma DualLeftHandedWeyl.contr_tmul_symm (φ : DualLeftHandedWeyl) (ψ : LeftHandedWeyl) :
    DualLeftHandedWeyl.contr (φ ⊗ₜ[ℂ] ψ) = LeftHandedWeyl.contr (ψ ⊗ₜ[ℂ] φ) := by
  rw [LeftHandedWeyl.contr_tmul_symm]

/-!

### A.4. Nondegeneracy

-/

/-- The contraction is nondegenerate: if `ψ^a φ_a = 0` for every `φ` then `ψ = 0`. -/
lemma LeftHandedWeyl.eq_zero_of_contr_tmul_eq_zero (ψ : LeftHandedWeyl)
    (h : ∀ φ, LeftHandedWeyl.contr (ψ ⊗ₜ φ) = 0) : ψ = 0 :=
  LeftHandedWeyl.toFin2ℂEquiv.injective <| funext fun j => by
    rw [map_zero]
    exact (LeftHandedWeyl.contr_tmul_basis ψ j).symm.trans (h _)

/-- The contraction is nondegenerate: if `φ_a ψ^a = 0` for every `ψ` then `φ = 0`. -/
lemma DualLeftHandedWeyl.eq_zero_of_contr_tmul_eq_zero (φ : DualLeftHandedWeyl)
    (h : ∀ ψ, DualLeftHandedWeyl.contr (φ ⊗ₜ ψ) = 0) : φ = 0 :=
  DualLeftHandedWeyl.toFin2ℂEquiv.injective <| funext fun j => by
    rw [map_zero, Pi.zero_apply, ← h (LeftHandedWeyl.basis j), DualLeftHandedWeyl.contr_tmul,
      LeftHandedWeyl.toFin2ℂ_eq_val, LeftHandedWeyl.basis_val, dotProduct_single, mul_one]

/-!

### A.5. Perfect pairing

-/

/-- The pairing `(ψ, φ) ↦ ψ^a φ_a` is perfect. It identifies dual-left-handed Weyl fermions with
  the dual of left-handed Weyl fermions, and vice versa. -/
instance LeftHandedWeyl.contrBi_isPerfPair : LeftHandedWeyl.contrBi.IsPerfPair :=
  .of_injective
    ((injective_iff_map_eq_zero _).2 fun ψ h =>
      LeftHandedWeyl.eq_zero_of_contr_tmul_eq_zero ψ fun φ => LinearMap.congr_fun h φ)
    ((injective_iff_map_eq_zero _).2 fun φ h =>
      DualLeftHandedWeyl.eq_zero_of_contr_tmul_eq_zero φ fun ψ => by
        rw [DualLeftHandedWeyl.contr_tmul_symm]
        exact LinearMap.congr_fun h ψ)

/-- The pairing `(φ, ψ) ↦ φ_a ψ^a` is perfect. It identifies left-handed Weyl fermions with the
  dual of dual-left-handed Weyl fermions, and vice versa. -/
instance DualLeftHandedWeyl.contrBi_isPerfPair : DualLeftHandedWeyl.contrBi.IsPerfPair :=
  .of_injective
    ((injective_iff_map_eq_zero _).2 fun φ h =>
      DualLeftHandedWeyl.eq_zero_of_contr_tmul_eq_zero φ fun ψ => LinearMap.congr_fun h ψ)
    ((injective_iff_map_eq_zero _).2 fun ψ h =>
      LeftHandedWeyl.eq_zero_of_contr_tmul_eq_zero ψ fun φ => by
        rw [LeftHandedWeyl.contr_tmul_symm]
        exact LinearMap.congr_fun h φ)

/-!

### A.6. Uniqueness up to scale

-/

/-- Every `SL(2,ℂ)`-invariant pairing of left-handed with dual-left-handed Weyl fermions is a
  multiple of `LeftHandedWeyl.contr`. -/
lemma LeftHandedWeyl.eq_smul_contr
    (B : (LeftHandedWeyl.rep.tprod DualLeftHandedWeyl.rep).IntertwiningMap
      (Representation.trivial ℂ SL(2,ℂ) ℂ)) :
    ∃ z : ℂ, B = z • LeftHandedWeyl.contr := by
  have hinv (C : (LeftHandedWeyl.rep.tprod DualLeftHandedWeyl.rep).IntertwiningMap
      (Representation.trivial ℂ SL(2,ℂ) ℂ)) (M : SL(2,ℂ)) (ψ φ) :
      C (LeftHandedWeyl.rep M ψ ⊗ₜ DualLeftHandedWeyl.rep M φ) = C (ψ ⊗ₜ φ) := by
    simpa using Representation.IntertwiningMap.isIntertwining _ _ C M (ψ ⊗ₜ φ)
  obtain ⟨T, hT⟩ : ∃ T : Module.End ℂ LeftHandedWeyl,
      ∀ ψ φ, B (ψ ⊗ₜ φ) = LeftHandedWeyl.contr (T ψ ⊗ₜ φ) :=
    ⟨LeftHandedWeyl.contrBi.toPerfPair.symm.toLinearMap ∘ₗ curry B.toLinearMap, fun ψ φ =>
      (LinearMap.congr_fun
        (LeftHandedWeyl.contrBi.apply_symm_toPerfPair_self (curry B.toLinearMap ψ)) φ).symm⟩
  obtain ⟨μ, hμ⟩ := LeftHandedWeyl.end_eq_smul_id_of_commute_rep (T := T) fun M =>
    LinearMap.ext fun ψ => sub_eq_zero.1 <|
      LeftHandedWeyl.eq_zero_of_contr_tmul_eq_zero _ fun φ => by
        rw [sub_tmul, map_sub, sub_eq_zero, LinearMap.comp_apply, LinearMap.comp_apply, ← hT,
          ← DualLeftHandedWeyl.rep.self_inv_apply M φ, hinv, hT, hinv]
  refine ⟨μ, Representation.IntertwiningMap.ext (TensorProduct.ext' fun ψ φ => ?_)⟩
  change B (ψ ⊗ₜ φ) = μ • LeftHandedWeyl.contr (ψ ⊗ₜ φ)
  rw [hT, hμ, LinearMap.smul_apply, LinearMap.id_apply, ← smul_tmul', map_smul]

/-- Every `SL(2,ℂ)`-invariant pairing of dual-left-handed with left-handed Weyl fermions is a
  multiple of `DualLeftHandedWeyl.contr`. -/
lemma DualLeftHandedWeyl.eq_smul_contr
    (B : (DualLeftHandedWeyl.rep.tprod LeftHandedWeyl.rep).IntertwiningMap
      (Representation.trivial ℂ SL(2,ℂ) ℂ)) :
    ∃ z : ℂ, B = z • DualLeftHandedWeyl.contr := by
  obtain ⟨z, hz⟩ := LeftHandedWeyl.eq_smul_contr
    (B.comp (Representation.TensorProduct.comm _ _).toIntertwiningMap)
  refine ⟨z, Representation.IntertwiningMap.ext (TensorProduct.ext' fun φ ψ => ?_)⟩
  change B (φ ⊗ₜ ψ) = z • DualLeftHandedWeyl.contr (φ ⊗ₜ ψ)
  rw [DualLeftHandedWeyl.contr_tmul_symm]
  exact congr($hz (ψ ⊗ₜ φ))

/-!

## B. Contractions of right-handed Weyl fermions

-/

/-!

### B.1. The contraction `ψ^{dot a} φ_{dot a}`

-/

/-- The bilinear map `(ψ, φ) ↦ ψ^{dot a} φ_{dot a}` underlying `RightHandedWeyl.contr`. -/
def RightHandedWeyl.contrBi : RightHandedWeyl →ₗ[ℂ] DualRightHandedWeyl →ₗ[ℂ] ℂ where
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
def RightHandedWeyl.contr : (RightHandedWeyl.rep.tprod DualRightHandedWeyl.rep).IntertwiningMap
    (Representation.trivial ℂ SL(2,ℂ) ℂ) where
  toLinearMap := TensorProduct.lift RightHandedWeyl.contrBi
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

lemma RightHandedWeyl.contr_tmul (ψ : RightHandedWeyl)
    (φ : DualRightHandedWeyl) :
    RightHandedWeyl.contr (ψ ⊗ₜ φ) = ψ.toFin2ℂ ⬝ᵥ φ.toFin2ℂ := by
  rfl

lemma RightHandedWeyl.contr_basis (i j : Fin 2) :
    RightHandedWeyl.contr (RightHandedWeyl.basis i ⊗ₜ DualRightHandedWeyl.basis j) =
    if i.1 = j.1 then (1 : ℂ) else 0 := by
  rw [RightHandedWeyl.contr_tmul]
  simp only [RightHandedWeyl.toFin2ℂ_eq_val, RightHandedWeyl.basis_val,
    DualRightHandedWeyl.toFin2ℂ_eq_val, DualRightHandedWeyl.basis_val, dotProduct_single, mul_one]
  rw [Pi.single_apply]
  simp only [Fin.ext_iff]
  refine ite_congr ?h₁ (congrFun rfl) (congrFun rfl)
  exact Eq.propIntro (fun a => id (Eq.symm a)) fun a => id (Eq.symm a)

/-- Contracting with the `j`-th basis vector picks out the `j`-th component. -/
lemma RightHandedWeyl.contr_tmul_basis (ψ : RightHandedWeyl) (j : Fin 2) :
    RightHandedWeyl.contr (ψ ⊗ₜ DualRightHandedWeyl.basis j) = ψ.val j := by
  rw [RightHandedWeyl.contr_tmul, DualRightHandedWeyl.toFin2ℂ_eq_val,
    DualRightHandedWeyl.basis_val, dotProduct_single, mul_one]
  rfl

/-!

### B.2. The contraction `φ_{dot a} ψ^{dot a}`

-/

/-- The bilinear map `(φ, ψ) ↦ φ_{dot a} ψ^{dot a}` underlying `DualRightHandedWeyl.contr`. -/
def DualRightHandedWeyl.contrBi : DualRightHandedWeyl →ₗ[ℂ] RightHandedWeyl →ₗ[ℂ] ℂ where
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
def DualRightHandedWeyl.contr : (DualRightHandedWeyl.rep.tprod RightHandedWeyl.rep).IntertwiningMap
    (Representation.trivial ℂ SL(2,ℂ) ℂ) where
  toLinearMap := TensorProduct.lift DualRightHandedWeyl.contrBi
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

lemma DualRightHandedWeyl.contr_tmul (φ : DualRightHandedWeyl)
    (ψ : RightHandedWeyl) :
    DualRightHandedWeyl.contr (φ ⊗ₜ ψ) = φ.toFin2ℂ ⬝ᵥ ψ.toFin2ℂ := by
  rfl

lemma DualRightHandedWeyl.contr_basis (i j : Fin 2) :
    DualRightHandedWeyl.contr (DualRightHandedWeyl.basis i ⊗ₜ RightHandedWeyl.basis j) =
    if i.1 = j.1 then (1 : ℂ) else 0 := by
  rw [DualRightHandedWeyl.contr_tmul]
  simp only [DualRightHandedWeyl.toFin2ℂ_eq_val, DualRightHandedWeyl.basis_val,
    RightHandedWeyl.toFin2ℂ_eq_val, RightHandedWeyl.basis_val, dotProduct_single, mul_one]
  rw [Pi.single_apply]
  simp only [Fin.ext_iff]
  refine ite_congr ?h₁ (congrFun rfl) (congrFun rfl)
  exact Eq.propIntro (fun a => id (Eq.symm a)) fun a => id (Eq.symm a)

/-!

### B.3. Symmetry

-/

lemma RightHandedWeyl.contr_tmul_symm (ψ : RightHandedWeyl) (φ : DualRightHandedWeyl) :
    RightHandedWeyl.contr (ψ ⊗ₜ[ℂ] φ) = DualRightHandedWeyl.contr (φ ⊗ₜ[ℂ] ψ) := by
  rw [RightHandedWeyl.contr_tmul, DualRightHandedWeyl.contr_tmul, dotProduct_comm]

lemma DualRightHandedWeyl.contr_tmul_symm (φ : DualRightHandedWeyl) (ψ : RightHandedWeyl) :
    DualRightHandedWeyl.contr (φ ⊗ₜ[ℂ] ψ) = RightHandedWeyl.contr (ψ ⊗ₜ[ℂ] φ) := by
  rw [RightHandedWeyl.contr_tmul_symm]

/-!

### B.4. Nondegeneracy

-/

/-- The contraction is nondegenerate: if `ψ^{dot a} φ_{dot a} = 0` for every `φ` then
  `ψ = 0`. -/
lemma RightHandedWeyl.eq_zero_of_contr_tmul_eq_zero (ψ : RightHandedWeyl)
    (h : ∀ φ, RightHandedWeyl.contr (ψ ⊗ₜ φ) = 0) : ψ = 0 :=
  RightHandedWeyl.toFin2ℂEquiv.injective <| funext fun j => by
    rw [map_zero]
    exact (RightHandedWeyl.contr_tmul_basis ψ j).symm.trans (h _)

/-- The contraction is nondegenerate: if `φ_{dot a} ψ^{dot a} = 0` for every `ψ` then
  `φ = 0`. -/
lemma DualRightHandedWeyl.eq_zero_of_contr_tmul_eq_zero (φ : DualRightHandedWeyl)
    (h : ∀ ψ, DualRightHandedWeyl.contr (φ ⊗ₜ ψ) = 0) : φ = 0 :=
  DualRightHandedWeyl.toFin2ℂEquiv.injective <| funext fun j => by
    rw [map_zero, Pi.zero_apply, ← h (RightHandedWeyl.basis j), DualRightHandedWeyl.contr_tmul,
      RightHandedWeyl.toFin2ℂ_eq_val, RightHandedWeyl.basis_val, dotProduct_single, mul_one]

/-!

### B.5. Perfect pairing

-/

/-- The pairing `(ψ, φ) ↦ ψ^{dot a} φ_{dot a}` is perfect. It identifies dual-right-handed Weyl
  fermions with the dual of right-handed Weyl fermions, and vice versa. -/
instance RightHandedWeyl.contrBi_isPerfPair : RightHandedWeyl.contrBi.IsPerfPair :=
  .of_injective
    ((injective_iff_map_eq_zero _).2 fun ψ h =>
      RightHandedWeyl.eq_zero_of_contr_tmul_eq_zero ψ fun φ => LinearMap.congr_fun h φ)
    ((injective_iff_map_eq_zero _).2 fun φ h =>
      DualRightHandedWeyl.eq_zero_of_contr_tmul_eq_zero φ fun ψ => by
        rw [DualRightHandedWeyl.contr_tmul_symm]
        exact LinearMap.congr_fun h ψ)

/-- The pairing `(φ, ψ) ↦ φ_{dot a} ψ^{dot a}` is perfect. It identifies right-handed Weyl
  fermions with the dual of dual-right-handed Weyl fermions, and vice versa. -/
instance DualRightHandedWeyl.contrBi_isPerfPair : DualRightHandedWeyl.contrBi.IsPerfPair :=
  .of_injective
    ((injective_iff_map_eq_zero _).2 fun φ h =>
      DualRightHandedWeyl.eq_zero_of_contr_tmul_eq_zero φ fun ψ => LinearMap.congr_fun h ψ)
    ((injective_iff_map_eq_zero _).2 fun ψ h =>
      RightHandedWeyl.eq_zero_of_contr_tmul_eq_zero ψ fun φ => by
        rw [RightHandedWeyl.contr_tmul_symm]
        exact LinearMap.congr_fun h φ)

/-!

### B.6. Uniqueness up to scale

The argument is that of A.6.

-/

/-- Every `SL(2,ℂ)`-invariant pairing of right-handed with dual-right-handed Weyl fermions is a
  multiple of `RightHandedWeyl.contr`. -/
lemma RightHandedWeyl.eq_smul_contr
    (B : (RightHandedWeyl.rep.tprod DualRightHandedWeyl.rep).IntertwiningMap
      (Representation.trivial ℂ SL(2,ℂ) ℂ)) :
    ∃ z : ℂ, B = z • RightHandedWeyl.contr := by
  have hinv (C : (RightHandedWeyl.rep.tprod DualRightHandedWeyl.rep).IntertwiningMap
      (Representation.trivial ℂ SL(2,ℂ) ℂ)) (M : SL(2,ℂ)) (ψ φ) :
      C (RightHandedWeyl.rep M ψ ⊗ₜ DualRightHandedWeyl.rep M φ) = C (ψ ⊗ₜ φ) := by
    simpa using Representation.IntertwiningMap.isIntertwining _ _ C M (ψ ⊗ₜ φ)
  obtain ⟨T, hT⟩ : ∃ T : Module.End ℂ RightHandedWeyl,
      ∀ ψ φ, B (ψ ⊗ₜ φ) = RightHandedWeyl.contr (T ψ ⊗ₜ φ) :=
    ⟨RightHandedWeyl.contrBi.toPerfPair.symm.toLinearMap ∘ₗ curry B.toLinearMap, fun ψ φ =>
      (LinearMap.congr_fun
        (RightHandedWeyl.contrBi.apply_symm_toPerfPair_self (curry B.toLinearMap ψ)) φ).symm⟩
  obtain ⟨μ, hμ⟩ := RightHandedWeyl.end_eq_smul_id_of_commute_rep (T := T) fun M =>
    LinearMap.ext fun ψ => sub_eq_zero.1 <|
      RightHandedWeyl.eq_zero_of_contr_tmul_eq_zero _ fun φ => by
        rw [sub_tmul, map_sub, sub_eq_zero, LinearMap.comp_apply, LinearMap.comp_apply, ← hT,
          ← DualRightHandedWeyl.rep.self_inv_apply M φ, hinv, hT, hinv]
  refine ⟨μ, Representation.IntertwiningMap.ext (TensorProduct.ext' fun ψ φ => ?_)⟩
  change B (ψ ⊗ₜ φ) = μ • RightHandedWeyl.contr (ψ ⊗ₜ φ)
  rw [hT, hμ, LinearMap.smul_apply, LinearMap.id_apply, ← smul_tmul', map_smul]

/-- Every `SL(2,ℂ)`-invariant pairing of dual-right-handed with right-handed Weyl fermions is a
  multiple of `DualRightHandedWeyl.contr`. -/
lemma DualRightHandedWeyl.eq_smul_contr
    (B : (DualRightHandedWeyl.rep.tprod RightHandedWeyl.rep).IntertwiningMap
      (Representation.trivial ℂ SL(2,ℂ) ℂ)) :
    ∃ z : ℂ, B = z • DualRightHandedWeyl.contr := by
  obtain ⟨z, hz⟩ := RightHandedWeyl.eq_smul_contr
    (B.comp (Representation.TensorProduct.comm _ _).toIntertwiningMap)
  refine ⟨z, Representation.IntertwiningMap.ext (TensorProduct.ext' fun φ ψ => ?_)⟩
  change B (φ ⊗ₜ ψ) = z • DualRightHandedWeyl.contr (φ ⊗ₜ ψ)
  rw [DualRightHandedWeyl.contr_tmul_symm]
  exact congr($hz (ψ ⊗ₜ φ))

end
end Fermion
