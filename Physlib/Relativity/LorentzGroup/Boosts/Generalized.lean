/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.LorentzGroup.Restricted.Basic
/-!

# Generalized Boosts

This module defines a generalization of the traditional boosts.
They are define given two velocities `u` and `v`, as an input an take
the velocity `u` to the velocity `v`.

We show that these generalised boosts are Lorentz transformations,
and furthermore sit in the restricted Lorentz group.

A boost is the special case of a generalised boost when `u = basis 0`.

## References

* The main argument follows: Guillem Cobos, The Lorentz Group, 2015:
  https://diposit.ub.edu/dspace/bitstream/2445/68763/2/memoria.pdf. [ref: cobos_2015_lorentz_group]
-/

@[expose] public section
noncomputable section

namespace LorentzGroup

open Lorentz
open TensorProduct
open Vector
variable {d : ℕ}

/-!

## Auxiliary Linear Maps

-/

/-- An auxiliary linear map used in the definition of a generalised boost. -/
def genBoostAux₁ (u v : Velocity d) : Vector d →ₗ[ℝ] Vector d where
  toFun x := (2 * ⟪x, u⟫ₘ) • v
  map_add' x y := by
    simp [map_add, mul_add, _root_.add_smul]
  map_smul' c x := by
    simp only [map_smul, RingHom.id_apply, smul_smul]
    simp only [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
    congr 1
    ring

/-- An auxiliary linear map used in the definition of a generalised boost. -/
def genBoostAux₂ (u v : Velocity d) : Vector d →ₗ[ℝ] Vector d where
  toFun x := - (⟪x, u.1 + v.1⟫ₘ / (1 + ⟪u.1, v.1⟫ₘ)) • (u.1 + v.1)
  map_add' x y := by
    rw [← _root_.add_smul]
    apply congrFun (congrArg _ _)
    have hx := Velocity.one_add_minkowskiProduct_ne_zero u v
    field_simp [add_tmul]
    simp only [map_add, add_apply, neg_add_rev]
    ring
  map_smul' c x := by
    rw [map_smul]
    simp only [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [smul_smul, mul_div_assoc, neg_mul_eq_mul_neg]

lemma genBoostAux₂_self (u : Velocity d) : genBoostAux₂ u u = - genBoostAux₁ u u := by
  ext1 x
  simp only [genBoostAux₂, LinearMap.coe_mk, AddHom.coe_mk, genBoostAux₁, LinearMap.neg_apply,
    map_add, Velocity.minkowskiProduct_self_eq_one]
  match_scalars
  ring

open minkowskiMatrix

lemma genBoostAux₁_apply_basis (u v : Velocity d) (μ : Fin 1 ⊕ Fin d) :
    (genBoostAux₁ u v) (Vector.basis μ) = (2 * η μ μ * u.1 μ) • v := by
  simp [genBoostAux₁]
  ring_nf

lemma genBoostAux₂_apply_basis (u v : Velocity d) (μ : Fin 1 ⊕ Fin d) :
    (genBoostAux₂ u v) (Vector.basis μ) =
    - (η μ μ * (u.1 μ + v.1 μ) / (1 + ⟪u.1, v.1⟫ₘ)) • (u.1 + v.1) := by
  simp [genBoostAux₂]
  ring_nf

lemma genBoostAux₁_basis_minkowskiProduct (u v : Velocity d) (μ ν : Fin 1 ⊕ Fin d) :
    ⟪genBoostAux₁ u v (Vector.basis μ), genBoostAux₁ u v (Vector.basis ν)⟫ₘ =
    4 * η μ μ * η ν ν * u.1 μ * u.1 ν := by
  simp [genBoostAux₁]
  ring

lemma genBoostAux₁_toMatrix_apply (u v : Velocity d) (μ ν : Fin 1 ⊕ Fin d) :
    (LinearMap.toMatrix Vector.basis Vector.basis (genBoostAux₁ u v)) μ ν =
    η ν ν * (2 * u.1 ν * v.1 μ) := by
  rw [LinearMap.toMatrix_apply, basis_repr_apply]
  simp only [genBoostAux₁, LinearMap.coe_mk, AddHom.coe_mk, minkowskiProduct_basis_left, apply_smul]
  ring

lemma genBoostAux₂_basis_minkowskiProduct (u v : Velocity d) (μ ν : Fin 1 ⊕ Fin d) :
    ⟪genBoostAux₂ u v (Vector.basis μ), genBoostAux₂ u v (Vector.basis ν)⟫ₘ =
    2 * η μ μ * η ν ν * (u.1 μ + v.1 μ) * (u.1 ν + v.1 ν)
    * (1 + ⟪u, v.1⟫ₘ)⁻¹ := by
  rw [genBoostAux₂_apply_basis, genBoostAux₂_apply_basis]
  rw [map_smul, map_smul]
  have h1 : ⟪u.1 + v.1, u.1 + v.1⟫ₘ = 2 * (1 + ⟪u.1, v.1⟫ₘ) := by
    simp only [map_add, add_apply, Velocity.minkowskiProduct_self_eq_one]
    rw [minkowskiProduct_symm]
    ring
  dsimp
  have h2 : (1 + ⟪u.1, v.1⟫ₘ) ≠ 0 := by
    exact Velocity.one_add_minkowskiProduct_ne_zero u v
  field_simp [h2]
  have h2 : (minkowskiProduct ↑v) u.1  = ⟪u.1, v.1⟫ₘ := by rw [minkowskiProduct_symm]
  simp only [map_add, _root_.smul_add, _root_.neg_smul, add_apply, _root_.neg_apply, smul_apply,
    Velocity.minkowskiProduct_self_eq_one, smul_eq_mul, h2]
  field_simp
  ring

lemma genBoostAux₁_basis_genBoostAux₂_minkowskiProduct (u v : Velocity d) (μ ν : Fin 1 ⊕ Fin d) :
    ⟪genBoostAux₁ u v (Vector.basis μ), genBoostAux₂ u v (Vector.basis ν)⟫ₘ =
    - 2 * η μ μ * η ν ν * u.1 μ * (u.1 ν + v.1 ν) := by
  rw [genBoostAux₁_apply_basis, genBoostAux₂_apply_basis]
  rw [map_smul, map_smul]
  have h1 : ⟪v.1, u.1 + v.1⟫ₘ = (1 + ⟪u.1, v.1⟫ₘ) := by
    simp only [map_add, Velocity.minkowskiProduct_self_eq_one]
    rw [minkowskiProduct_symm]
    ring
  simp only [smul_apply, map_add, Velocity.minkowskiProduct_self_eq_one, smul_eq_mul, neg_mul,
    neg_inj]
  have h2 : (1 + ⟪u.1, v.1⟫ₘ) ≠ 0 := by
    exact Velocity.one_add_minkowskiProduct_ne_zero u v
  field_simp [h2]
  rw [minkowskiProduct_symm]
  ring

lemma genBoostAux₂_toMatrix_apply (u v : Velocity d) (μ ν : Fin 1 ⊕ Fin d) :
    (LinearMap.toMatrix Vector.basis Vector.basis (genBoostAux₂ u v)) μ ν =
      η ν ν * (- (u.1 μ + v.1 μ) * (u.1 ν + v.1 ν)
      / (1 + ⟪u.1, v.1⟫ₘ)) := by
  rw [LinearMap.toMatrix_apply, basis_repr_apply]
  simp only [genBoostAux₂, LinearMap.coe_mk, AddHom.coe_mk, minkowskiProduct_basis_left]
  have h1 := Velocity.one_add_minkowskiProduct_ne_zero u v
  simp only [apply_add, apply_smul, neg_mul, neg_add_rev]
  field_simp
  ring

lemma genBoostAux₁_add_genBoostAux₂_minkowskiProduct (u v : Velocity d) (μ ν : Fin 1 ⊕ Fin d) :
    ⟪genBoostAux₁ u v (Vector.basis μ) + genBoostAux₂ u v (Vector.basis μ),
    genBoostAux₁ u v (Vector.basis ν) + genBoostAux₂ u v (Vector.basis ν)⟫ₘ =
    2 * η μ μ * η ν ν * (- u.1 μ * (u.1 ν + v.1 ν)
      - u.1 ν * (u.1 μ + v.1 μ)
      + (u.1 μ + v.1 μ) * (u.1 ν + v.1 ν) * (1 + ⟪u, v.1⟫ₘ)⁻¹ +
      2 * u.1 μ * u.1 ν) := by
  conv_lhs =>
    simp only [map_add, add_apply]
    rw [genBoostAux₁_basis_minkowskiProduct, genBoostAux₂_basis_minkowskiProduct,
      genBoostAux₁_basis_genBoostAux₂_minkowskiProduct,
      minkowskiProduct_symm,
      genBoostAux₁_basis_genBoostAux₂_minkowskiProduct]
  ring

lemma basis_minkowskiProduct_genBoostAux₁_add_genBoostAux₂ (u v : Velocity d)
    (μ ν : Fin 1 ⊕ Fin d) :
    ⟪Vector.basis μ, genBoostAux₁ u v (Vector.basis ν) + genBoostAux₂ u v (Vector.basis ν)⟫ₘ =
    η μ μ * η ν ν * (2 * u.1 ν * v.1 μ
    - (u.1 μ + v.1 μ) * (u.1 ν + v.1 ν) * (1 + ⟪u.1, v.1⟫ₘ)⁻¹) := by
  conv_lhs =>
    rw [map_add]
    rw [genBoostAux₁_apply_basis, genBoostAux₂_apply_basis]
    rw [map_smul, map_smul]
    simp
  have h2 : (1 + ⟪u.1, v.1⟫ₘ) ≠ 0 := by
    exact Velocity.one_add_minkowskiProduct_ne_zero u v
  field_simp
  ring

/-!

## Generalized Boosts

-/

/-- An generalised boost. This is a Lorentz transformation which takes the Lorentz velocity `u`
  to `v`. -/
def generalizedBoost (u v : Velocity d) : LorentzGroup d :=
  ⟨LinearMap.toMatrix Vector.basis Vector.basis
    (LinearMap.id + genBoostAux₁ u v + genBoostAux₂ u v), by
  rw [← isLorentz_iff_toMatrix_mem_lorentzGroup]
  rw [isLorentz_iff_basis]
  intro μ ν
  trans ⟪(basis μ) + (genBoostAux₁ u v (basis μ) + genBoostAux₂ u v (basis μ)),
    (basis ν) + (genBoostAux₁ u v (basis ν) + genBoostAux₂ u v (basis ν))⟫ₘ
  · simp only [LinearMap.add_apply, LinearMap.id_coe, id_eq, map_add,
    add_apply, minkowskiProduct_basis_right, basis_apply, mul_ite, mul_one,
    MulZeroClass.mul_zero, minkowskiProduct_basis_left]
    ring
  rw [map_add]
  conv_lhs =>
    enter [1]
    rw [map_add]
    simp only [add_apply]
    enter [2]
    rw [minkowskiProduct_symm, basis_minkowskiProduct_genBoostAux₁_add_genBoostAux₂]
  conv_lhs =>
    enter [2, 1]
    rw [map_add]
  conv_lhs =>
    enter [2]
    simp only [add_apply]
    rw [basis_minkowskiProduct_genBoostAux₁_add_genBoostAux₂,
      genBoostAux₁_add_genBoostAux₂_minkowskiProduct]
  ring⟩

lemma generalizedBoost_apply (u v : Velocity d) (x : Vector d) :
    generalizedBoost u v • x = x + genBoostAux₁ u v x + genBoostAux₂ u v x:= by
  rw [smul_eq_mulVec]
  simp [generalizedBoost]
  rw [Matrix.add_mulVec, Matrix.add_mulVec]
  simp only [Matrix.one_mulVec]
  congr
  · rw [map_apply_eq_basis_mulVec]
  · rw [map_apply_eq_basis_mulVec]

lemma generalizedBoost_apply_mul_one_plus_contr (u v : Velocity d) (x : Vector d) :
    (1 + ⟪u, v.1⟫ₘ) • generalizedBoost u v • x = (1 + ⟪u, v.1⟫ₘ) • x +
    (2 * ⟪x, u⟫ₘ * (1 + ⟪u, v.1⟫ₘ)) • v - ⟪x, u + v⟫ₘ • (u + v) := by
  rw [generalizedBoost_apply, _root_.smul_add, _root_.smul_add]
  trans (1 + ⟪u, v.1⟫ₘ) • x + (2 * ⟪x, u⟫ₘ * (1 + ⟪u, v.1⟫ₘ)) • v
    + (- ⟪x, u + v⟫ₘ) • (u + v)
  · congr 1
    · congr 1
      rw [genBoostAux₁]
      simp only [LinearMap.coe_mk, AddHom.coe_mk]
      rw [smul_smul]
      congr 1
      ring
    · rw [genBoostAux₂]
      simp only [LinearMap.coe_mk, AddHom.coe_mk]
      rw [smul_smul]
      congr
      have h1 := Velocity.one_add_minkowskiProduct_ne_zero u v
      field_simp
  · rw [_root_.neg_smul]
    rfl

lemma generalizedBoost_apply_expand (u v : Velocity d) (x : Vector d) :
    generalizedBoost u v • x = x + (2 * ⟪x, u⟫ₘ) • v.1 -
      (⟪x, u + v⟫ₘ / (1 + ⟪u, v.1⟫ₘ)) • (u.1 + v.1) := by
  have h := Velocity.one_add_minkowskiProduct_ne_zero u v
  apply (smul_right_inj h).mp
  rw [generalizedBoost_apply_mul_one_plus_contr]
  match_scalars <;> field_simp

@[simp]
lemma generalizedBoost_apply_fst (u v : Velocity d) :
    generalizedBoost u v • u.1 = v.1 := by
  apply (smul_right_inj (Velocity.one_add_minkowskiProduct_ne_zero u v)).mp
  rw [generalizedBoost_apply_mul_one_plus_contr]
  simp only [Velocity.minkowskiProduct_self_eq_one, map_add]
  match_scalars <;> ring

@[simp]
lemma generalizedBoost_apply_snd (u v : Velocity d) :
    generalizedBoost u v • v.1 = (2 * ⟪u, v.1⟫ₘ) • ↑v - ↑u:= by
  apply (smul_right_inj (Velocity.one_add_minkowskiProduct_ne_zero u v)).mp
  rw [generalizedBoost_apply_mul_one_plus_contr]
  simp only [map_add, Velocity.minkowskiProduct_self_eq_one,
    minkowskiProduct_symm v.1 u.1]
  match_scalars <;> ring

/-- This lemma states that for a given four-velocity `u`, the general boost
  transformation `genBoost u u` is equal to the identity linear map `LinearMap.id`.
-/
@[simp]
lemma generalizedBoost_self (u : Velocity d) :
    generalizedBoost u u = 1 := by
  refine SetCoe.ext ?_
  simp [generalizedBoost, genBoostAux₂_self]

lemma genearlizedBoost_apply_basis (u v : Velocity d) (μ : Fin 1 ⊕ Fin d) :
    generalizedBoost u v • (Vector.basis μ) =
    Vector.basis μ + (2 * η μ μ * u.1 μ) • v - (η μ μ * (u.1 μ + v.1 μ)
      / (1 + ⟪u.1, v.1⟫ₘ)) • (u.1 + v.1) := by
  rw [generalizedBoost_apply, genBoostAux₁_apply_basis, genBoostAux₂_apply_basis]
  module

lemma generalizedBoost_apply_eq_minkowskiProduct (u v : Velocity d) (μ ν : Fin 1 ⊕ Fin d) :
    (generalizedBoost u v).1 μ ν = η μ μ * (⟪Vector.basis μ, Vector.basis ν⟫ₘ + 2 *
    ⟪Vector.basis ν, u⟫ₘ * ⟪Vector.basis μ, v.1⟫ₘ
    - ⟪Vector.basis μ, u + v⟫ₘ * ⟪Vector.basis ν, u + v⟫ₘ / (1 + ⟪u.1, v⟫ₘ)) := by
  conv_lhs =>
    rw [generalizedBoost]
    simp
  conv_rhs =>
    rw [mul_sub, mul_add]
  congr
  · simp
    by_cases h : μ = ν
    · subst h
      simp
    · simp [h]
  · rw [genBoostAux₁_toMatrix_apply u v μ ν]
    simp only [minkowskiProduct_basis_left]
    ring_nf
    simp
  · rw [genBoostAux₂_toMatrix_apply u v μ ν]
    simp only [neg_add_rev, map_add, minkowskiProduct_basis_left]
    ring_nf
    simp

lemma generalizedBoost_apply_eq_toCoord (u v : Velocity d) (μ ν : Fin 1 ⊕ Fin d) :
    (generalizedBoost u v).1 μ ν = ((1 : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ) μ ν +
    2 * η ν ν * u.1 ν * v.1 μ
    - η ν ν * (u.1 μ + v.1 μ) * (u.1 ν + v.1 ν) / (1 + ⟪u.1, v⟫ₘ)) := by
  conv_lhs =>
    rw [generalizedBoost]
    simp
  congr
  · rw [genBoostAux₁_toMatrix_apply u v μ ν]
    ring_nf
  · rw [genBoostAux₂_toMatrix_apply u v μ ν]
    simp only [neg_add_rev]
    ring_nf

@[fun_prop]
lemma generalizedBoost_continuous_snd (u : Velocity d) : Continuous (generalizedBoost u) := by
  have : Continuous (fun v => (generalizedBoost u v).1) := by
    refine continuous_matrix ?_
    intro i j
    simp only [generalizedBoost_apply_eq_minkowskiProduct]
    fun_prop (disch := exact fun x => Velocity.one_add_minkowskiProduct_ne_zero u x)
  refine Continuous.subtype_mk this _

@[fun_prop]
lemma generalizedBoost_continuous_fst (u : Velocity d) : Continuous (generalizedBoost · u) := by
  have : Continuous (fun v => (generalizedBoost v u).1) := by
    refine continuous_matrix ?_
    intro i j
    simp only [generalizedBoost_apply_eq_minkowskiProduct]
    fun_prop (disch := exact fun x => Velocity.one_add_minkowskiProduct_ne_zero x u)
  refine Continuous.subtype_mk this _

lemma id_joined_generalizedBoost (u v : Velocity d) : Joined 1 (generalizedBoost u v) := by
  obtain ⟨f, _⟩ := Velocity.isPathConnected.joinedIn u trivial v trivial
  use ContinuousMap.comp ⟨generalizedBoost u, by fun_prop⟩ f
  · simp
  · simp

lemma generalizedBoost_in_connected_component_of_id (u v : Velocity d) :
    generalizedBoost u v ∈ connectedComponent 1 :=
  pathComponent_subset_component _ (id_joined_generalizedBoost u v)

lemma generalizedBoost_isProper (u v : Velocity d) : IsProper (generalizedBoost u v) :=
  (isProper_on_connected_component
    (generalizedBoost_in_connected_component_of_id u v)).mp isProper_id

lemma generalizedBoost_isOrthochronous (u v : Velocity d) :
    IsOrthochronous (generalizedBoost u v) :=
  (isOrthochronous_on_connected_component (generalizedBoost_in_connected_component_of_id u v)).mp
    id_isOrthochronous

lemma generalizedBoost_mem_restricted (u v : Velocity d) :
    generalizedBoost u v ∈ LorentzGroup.restricted d := by
  rw [LorentzGroup.restricted]
  apply And.intro
  · exact generalizedBoost_isProper u v
  · exact generalizedBoost_isOrthochronous u v

lemma generalizedBoost_inv (u v : Velocity d) :
    (generalizedBoost u v)⁻¹ = generalizedBoost v u := by
  rw [← mul_eq_one_iff_inv_eq']
  apply LorentzGroup.eq_of_action_vector_eq
  intro p
  have h1 := Velocity.one_add_minkowskiProduct_ne_zero u v
  rw [SemigroupAction.mul_smul]
  simp only [generalizedBoost_apply_expand, map_add, map_sub, map_smul, add_apply, sub_apply,
    smul_apply, smul_eq_mul, Velocity.minkowskiProduct_self_eq_one, one_smul,
    minkowskiProduct_symm v.1 u.1]
  match_scalars <;> field_simp <;> ring

/-- The time component of a generalised boost. -/
lemma generalizedBoost_timeComponent_eq (u v : Velocity d) :
    (generalizedBoost u v).1 (Sum.inl 0) (Sum.inl 0) = 1 +
    ‖u.1.timeComponent • v.1.spatialPart -
      v.1.timeComponent • u.1.spatialPart‖ ^ 2 / (1 + ⟪u.1, v.1⟫ₘ) := by
  rw [generalizedBoost_apply_eq_toCoord]
  simp only [Matrix.one_apply_eq, inl_0_inl_0, one_mul]
  have h := Velocity.one_add_minkowskiProduct_ne_zero u v
  rw [norm_sub_sq_real, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    Velocity.timeComponent_abs u, Velocity.timeComponent_abs v,
    real_inner_smul_left, real_inner_smul_right]
  simp only [timeComponent, minkowskiProduct_eq_timeComponent_spatialPart] at *
  field_simp [h]
  nlinarith [mul_pow (u.1 (Sum.inl 0)) (‖v.1.spatialPart‖) 2,
            mul_pow (v.1 (Sum.inl 0)) (‖u.1.spatialPart‖) 2,
            Velocity.norm_spatialPart_sq_eq u, Velocity.norm_spatialPart_sq_eq v,
            real_inner_comm (u.1.spatialPart) (v.1.spatialPart)]

end LorentzGroup

end
