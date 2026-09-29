/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.Tensors.RealTensor.Vector.Pre.Basic
public import Mathlib.RepresentationTheory.Rep.Basic
/-!

# Contraction of Real Lorentz vectors

-/

@[expose] public section

noncomputable section

open Matrix
open MatrixGroups
open Complex
open TensorProduct
open CategoryTheory.MonoidalCategory
open minkowskiMatrix

namespace Lorentz

variable {d : ℕ}

/-- The bi-linear map corresponding to contraction of a contravariant Lorentz vector with a
  covariant Lorentz vector. -/
def contrModCoModBi (d : ℕ) : ContrMod d →ₗ[ℝ] CoMod d →ₗ[ℝ] ℝ where
  toFun ψ := {
    toFun := fun φ => ψ.toFin1dℝ ⬝ᵥ φ.toFin1dℝ,
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

/-- The bi-linear map corresponding to contraction of a covariant Lorentz vector with a
  contravariant Lorentz vector. -/
def coModContrModBi (d : ℕ) : CoMod d →ₗ[ℝ] ContrMod d →ₗ[ℝ] ℝ where
  toFun φ := {
    toFun := fun ψ => φ.toFin1dℝ ⬝ᵥ ψ.toFin1dℝ,
    map_add' := by
      intro ψ ψ'
      simp only [map_add]
      rw [dotProduct_add]
    map_smul' := by
      intro r ψ
      simp only [LinearEquiv.map_smul]
      rw [dotProduct_smul]
      rfl}
  map_add' φ φ' := by
    refine LinearMap.ext (fun ψ => ?_)
    simp only [map_add, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply]
    rw [add_dotProduct]
  map_smul' r φ := by
    refine LinearMap.ext (fun ψ => ?_)
    simp only [LinearEquiv.map_smul, LinearMap.coe_mk, AddHom.coe_mk]
    rw [smul_dotProduct]
    rfl

/-- The linear map from ContrMod d ⊗ CoMod d to ℝ given by
    summing over components of contravariant Lorentz vector and
    covariant Lorentz vector in the
    standard basis (i.e. the dot product).
    In terms of index notation this is the contraction is ψⁱ φᵢ. -/
def contrCoContract : ((ContrMod.rep).tprod (CoMod.rep)).IntertwiningMap
    (Representation.trivial ℝ (LorentzGroup d) ℝ) where
  toLinearMap := TensorProduct.lift (contrModCoModBi d)
  isIntertwining' Λ := by
    ext ψ φ
    simp only [Representation.tprod_apply, AlgebraTensorModule.curry_apply,
      LinearMap.restrictScalars_self, curry_apply, LinearMap.coe_comp, Function.comp_apply,
      map_tmul, lift.tmul, Representation.isTrivial_def, LinearMap.id_comp]
    change (Λ.1 *ᵥ ψ.toFin1dℝ) ⬝ᵥ ((LorentzGroup.transpose Λ⁻¹).1 *ᵥ φ.toFin1dℝ) = _
    rw [dotProduct_mulVec, LorentzGroup.transpose_val,
      vecMul_transpose, mulVec_mulVec, LorentzGroup.coe_inv, inv_mul_of_invertible Λ.1]
    simp only [one_mulVec]
    rfl

/-- Notation for `contrCoContract` acting on a tmul. -/
local notation "⟪" ψ "," φ "⟫ₘ" => contrCoContract (ψ ⊗ₜ φ)

lemma contrCoContract_hom_tmul (ψ : ContrMod d) (φ : CoMod d) :
    ⟪ψ, φ⟫ₘ = ψ.toFin1dℝ ⬝ᵥ φ.toFin1dℝ := by
  rfl

/-- The linear map from CoMod d ⊗ ContrMod d to ℝ given by
    summing over components of contravariant Lorentz vector and
    covariant Lorentz vector in the
    standard basis (i.e. the dot product).
    In terms of index notation this is the contraction is ψⁱ φᵢ. -/
def coContrContract : ((CoMod.rep (d := d)).tprod (ContrMod.rep (d := d))).IntertwiningMap
    (Representation.trivial ℝ (LorentzGroup d) ℝ) where
  toLinearMap := TensorProduct.lift (coModContrModBi d)
  isIntertwining' Λ := by
    ext ψ φ
    change ((LorentzGroup.transpose Λ⁻¹).1 *ᵥ ψ.toFin1dℝ) ⬝ᵥ (Λ.1 *ᵥ φ.toFin1dℝ) = _
    rw [dotProduct_mulVec, LorentzGroup.transpose_val, mulVec_transpose, vecMul_vecMul,
      LorentzGroup.coe_inv, inv_mul_of_invertible Λ.1]
    simp only [vecMul_one]
    rfl

/-- Notation for `coContrContract` acting on a tmul. -/
local notation "⟪" φ "," ψ "⟫ₘ" => coContrContract (φ ⊗ₜ ψ)

lemma coContrContract_hom_tmul (φ : CoMod d) (ψ : ContrMod d) :
    ⟪φ, ψ⟫ₘ = φ.toFin1dℝ ⬝ᵥ ψ.toFin1dℝ := by
  rfl

/-!

## Symmetry relations

-/

lemma contrCoContract_tmul_symm (φ : ContrMod d) (ψ : CoMod d) : ⟪φ, ψ⟫ₘ = ⟪ψ, φ⟫ₘ := by
  rw [contrCoContract_hom_tmul, coContrContract_hom_tmul, dotProduct_comm]

lemma coContrContract_tmul_symm (φ : CoMod d) (ψ : ContrMod d) : ⟪φ, ψ⟫ₘ = ⟪ψ, φ⟫ₘ := by
  rw [contrCoContract_tmul_symm]

/-!

## Contracting contr vectors with contr vectors etc.

-/
open CategoryTheory.MonoidalCategory
open CategoryTheory

/-- The linear map from ContrMod d ⊗ ContrMod d to ℝ induced by the homomorphism
  `Contr.toCo` and the contraction `contrCoContract`. -/
def contrContrContract : ((ContrMod.rep (d := d)).tprod (ContrMod.rep (d := d))).IntertwiningMap
    (Representation.trivial ℝ (LorentzGroup d) ℝ) := contrCoContract.comp
  ((Contr.toCo d).lTensor (ContrMod.rep (d := d)))

/-- The linear map from ContrMod d ⊗ ContrMod d to ℝ induced by the homomorphism
  `Contr.toCo` and the contraction `contrCoContract`. -/
def contrContrContractField : ContrMod d ⊗[ℝ] ContrMod d →ₗ[ℝ] ℝ :=
  contrContrContract.toLinearMap

/-- Notation for `contrContrContractField` acting on a tmul. -/
local notation "⟪" ψ "," φ "⟫ₘ" => contrContrContractField (ψ ⊗ₜ φ)

lemma contrContrContract_hom_tmul (φ : ContrMod d) (ψ : ContrMod d) :
    ⟪φ, ψ⟫ₘ = φ.toFin1dℝ ⬝ᵥ η *ᵥ ψ.toFin1dℝ:= by
  simp only [contrContrContractField]
  erw [contrCoContract_hom_tmul]
  rfl

/-- The linear map from CoMod d ⊗ CoMod d to ℝ induced by the homomorphism
  `Co.toContr` and the contraction `coContrContract`. -/
def coCoContract : ((CoMod.rep (d := d)).tprod (CoMod.rep (d := d))).IntertwiningMap
    (Representation.trivial ℝ (LorentzGroup d) ℝ) := coContrContract.comp
    ((Co.toContr d).lTensor (CoMod.rep (d := d)))

/-- Notation for `coCoContract` acting on a tmul. -/
local notation "⟪" ψ "," φ "⟫ₘ" => coCoContract (ψ ⊗ₜ φ)

lemma coCoContract_hom_tmul (φ : CoMod d) (ψ : CoMod d) :
    ⟪φ, ψ⟫ₘ = φ.toFin1dℝ ⬝ᵥ η *ᵥ ψ.toFin1dℝ := by rfl

/-!

## Lemmas related to contraction.

We derive the lemmas in main for `contrContrContractField`.

-/
namespace contrContrContractField

variable (x y : ContrMod d)

@[simp]
lemma action_tmul (g : LorentzGroup d) : ⟪ContrMod.rep g x, ContrMod.rep g y⟫ₘ = ⟪x, y⟫ₘ :=
  LinearMap.congr_fun (contrContrContract.isIntertwining' g) (x ⊗ₜ[ℝ] y)

lemma as_sum : ⟪x, y⟫ₘ = x.val (Sum.inl 0) * y.val (Sum.inl 0) -
    ∑ i, x.val (Sum.inr i) * y.val (Sum.inr i) := by
  rw [contrContrContract_hom_tmul]
  simp only [dotProduct, minkowskiMatrix, LieAlgebra.Orthogonal.indefiniteDiagonal, mulVec_diagonal,
    Fintype.sum_sum_type, Finset.univ_unique, Fin.default_eq_zero, Fin.isValue, Sum.elim_inl,
    one_mul, Finset.sum_singleton, Sum.elim_inr, neg_mul, mul_neg, Finset.sum_neg_distrib]
  rfl

open InnerProductSpace

lemma as_sum_toSpace : ⟪x, y⟫ₘ = x.val (Sum.inl 0) * y.val (Sum.inl 0) -
    ⟪x.toSpace, y.toSpace⟫_ℝ := by
  rw [as_sum]
  congr
  funext i
  rw [mul_comm]
  rfl

lemma stdBasis_inl {d : ℕ} :
    ⟪@ContrMod.stdBasis d (Sum.inl 0), ContrMod.stdBasis (Sum.inl 0)⟫ₘ = (1 : ℝ) := by
  rw [as_sum]
  trans (1 : ℝ) - (0 : ℝ)
  congr
  · rw [ContrMod.stdBasis_apply_same]
    simp
  · rw [Fintype.sum_eq_zero]
    intro a
    simp
  · ring

lemma symm : ⟪x, y⟫ₘ = ⟪y, x⟫ₘ := by
  rw [as_sum, as_sum]
  congr 1
  rw [mul_comm]
  congr
  funext i
  rw [mul_comm]

lemma dual_mulVec_right : ⟪x, dual Λ *ᵥ y⟫ₘ = ⟪Λ *ᵥ x, y⟫ₘ := by
  rw [contrContrContract_hom_tmul, contrContrContract_hom_tmul]
  simp only [ContrMod.mulVec_toFin1dℝ, mulVec_mulVec]
  simp only [dual, ← mul_assoc, minkowskiMatrix.sq, one_mul]
  rw [← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]

lemma dual_mulVec_left : ⟪dual Λ *ᵥ x, y⟫ₘ = ⟪x, Λ *ᵥ y⟫ₘ := by
  rw [symm, dual_mulVec_right, symm]

lemma right_parity : ⟪x, ContrMod.rep LorentzGroup.parity y⟫ₘ = ∑ i, x.val i * y.val i := by
  rw [as_sum]
  simp only [Fin.isValue, Fintype.sum_sum_type, Finset.univ_unique, Fin.default_eq_zero,
    Finset.sum_singleton]
  trans x.val (Sum.inl 0) * ((ContrMod.rep LorentzGroup.parity) y).val (Sum.inl 0) +
    ∑ i : Fin d, - (x.val (Sum.inr i) * ((ContrMod.rep LorentzGroup.parity) y).val (Sum.inr i))
  · simp only [Fin.isValue, Finset.sum_neg_distrib]
    rfl
  congr 1
  · change x.val (Sum.inl 0) * (η *ᵥ y.toFin1dℝ) (Sum.inl 0) = _
    simp only [Fin.isValue, mulVec_inl_0, mul_eq_mul_left_iff]
    exact mul_eq_mul_left_iff.mp rfl
  · congr
    funext i
    change - (x.val (Sum.inr i) * ((η *ᵥ y.toFin1dℝ) (Sum.inr i))) = _
    simp only [mulVec_inr_i, mul_neg, neg_neg, mul_eq_mul_left_iff]
    exact mul_eq_mul_left_iff.mp rfl

lemma self_parity_eq_zero_iff : ⟪y, ContrMod.rep LorentzGroup.parity y⟫ₘ = 0 ↔ y = 0 := by
  refine Iff.intro (fun h => ?_) (fun h => ?_)
  · rw [right_parity] at h
    have hn := Fintype.sum_eq_zero_iff_of_nonneg (f := fun i => y.val i * y.val i) (fun i => by
      simpa using mul_self_nonneg (y.val i))
    rw [h] at hn
    simp only [true_iff] at hn
    apply ContrMod.ext
    funext i
    have h1 := congrFun hn i
    simp only [Pi.zero_apply, mul_eq_zero, or_self] at h1
    simp only [h1]
    rfl
  · rw [h]
    simp only [map_zero, tmul_zero]

/-- The metric tensor is non-degenerate. -/
lemma nondegenerate : (∀ (x : ContrMod d), ⟪x, y⟫ₘ = 0) ↔ y = 0 := by
  refine Iff.intro (fun h => ?_) (fun h => ?_)
  · exact (self_parity_eq_zero_iff _).mp ((symm _ _).trans $ h _)
  · simp [h]

lemma matrix_apply_eq_iff_sub : ⟪x, Λ *ᵥ y⟫ₘ = ⟪x, Λ' *ᵥ y⟫ₘ ↔ ⟪x, (Λ - Λ') *ᵥ y⟫ₘ = 0 := by
  rw [← sub_eq_zero, ← LinearMap.map_sub, ← tmul_sub, ← ContrMod.sub_mulVec Λ Λ' y]

lemma matrix_eq_iff_eq_forall' : (∀ (v : ContrMod d), (Λ *ᵥ v) = Λ' *ᵥ v) ↔
    ∀ (w v : ContrMod d), ⟪v, Λ *ᵥ w⟫ₘ = ⟪v, Λ' *ᵥ w⟫ₘ := by
  refine Iff.intro (fun h ↦ fun w v ↦ ?_) (fun h ↦ fun v ↦ ?_)
  · rw [h w]
  · simp only [matrix_apply_eq_iff_sub] at h
    refine sub_eq_zero.1 ?_
    have h1 := h v
    rw [nondegenerate] at h1
    simp only [ContrMod.sub_mulVec] at h1
    exact h1

lemma matrix_eq_iff_eq_forall : Λ = Λ' ↔ ∀ (w v : ContrMod d), ⟪v, Λ *ᵥ w⟫ₘ = ⟪v, Λ' *ᵥ w⟫ₘ := by
  rw [← matrix_eq_iff_eq_forall']
  refine Iff.intro (fun h => ?_) (fun h => ?_)
  · subst h
    exact fun v => rfl
  · rw [← (LinearMap.toMatrix ContrMod.stdBasis ContrMod.stdBasis).toEquiv.symm.apply_eq_iff_eq]
    ext1 v
    exact h v

lemma matrix_eq_id_iff : Λ = 1 ↔ ∀ (w v : ContrMod d), ⟪v, Λ *ᵥ w⟫ₘ = ⟪v, w⟫ₘ := by
  rw [matrix_eq_iff_eq_forall]
  simp only [ContrMod.one_mulVec]

lemma _root_.LorentzGroup.mem_iff_invariant : Λ ∈ LorentzGroup d ↔
    ∀ (w v : ContrMod d), ⟪Λ *ᵥ v, Λ *ᵥ w⟫ₘ = ⟪v, w⟫ₘ := by
  refine Iff.intro (fun h => ?_) (fun h => ?_)
  · intro x y
    rw [← dual_mulVec_right, ContrMod.mulVec_mulVec]
    have h1 := LorentzGroup.mem_iff_dual_mul_self.mp h
    rw [h1]
    rw [ContrMod.one_mulVec]
  · conv at h =>
      intro x y
      rw [← dual_mulVec_right, ContrMod.mulVec_mulVec]
    rw [← matrix_eq_id_iff] at h
    exact LorentzGroup.mem_iff_dual_mul_self.mpr h

lemma _root_.LorentzGroup.mem_iff_norm : Λ ∈ LorentzGroup d ↔
    ∀ (w : ContrMod d), ⟪Λ *ᵥ w, Λ *ᵥ w⟫ₘ = ⟪w, w⟫ₘ := by
  rw [LorentzGroup.mem_iff_invariant]
  refine Iff.intro (fun h x => h x x) (fun h x y => ?_)
  have hp := h (x + y)
  have hn := h (x - y)
  rw [ContrMod.mulVec_add, tmul_add, add_tmul, add_tmul, tmul_add, add_tmul, add_tmul] at hp
  rw [ContrMod.mulVec_sub, tmul_sub, sub_tmul, sub_tmul, tmul_sub, sub_tmul, sub_tmul] at hn
  simp only [map_add, map_sub] at hp hn
  rw [symm (Λ *ᵥ y) (Λ *ᵥ x), symm y x] at hp hn
  let e : 𝟙_ (Rep ℝ ↑(LorentzGroup d)) ≃ₗ[ℝ] ℝ :=
    LinearEquiv.refl ℝ ((𝟙_ (Rep ℝ ↑(LorentzGroup d))))
  apply e.injective
  have hp' := e.injective.eq_iff.mpr hp
  have hn' := e.injective.eq_iff.mpr hn
  simp only [map_add, map_sub] at hp' hn'
  linear_combination (norm := ring_nf) (1 / 4) * hp' + (-1/ 4) * hn'
  rw [symm (Λ *ᵥ y) (Λ *ᵥ x), symm y x]
  simp

/-!

## Some equalities and inequalities

-/

lemma inl_sq_eq (v : ContrMod d) : v.val (Sum.inl 0) ^ 2 =
    (⟪v, v⟫ₘ) + ∑ i, v.val (Sum.inr i) ^ 2:= by
  rw [as_sum]
  apply sub_eq_iff_eq_add.mp
  congr
  · exact pow_two (v.val (Sum.inl 0))
  · funext i
    exact pow_two (v.val (Sum.inr i))

lemma le_inl_sq (v : ContrMod d) : ⟪v, v⟫ₘ ≤ v.val (Sum.inl 0) ^ 2 := by
  rw [inl_sq_eq]
  apply (le_add_iff_nonneg_right _).mpr
  refine Fintype.sum_nonneg ?hf
  exact fun i => pow_two_nonneg (v.val (Sum.inr i))

lemma ge_abs_inner_product (v w : ContrMod d) : v.val (Sum.inl 0) * w.val (Sum.inl 0) -
    ‖⟪v.toSpace, w.toSpace⟫_ℝ‖ ≤ ⟪v, w⟫ₘ := by
  rw [as_sum_toSpace, sub_le_sub_iff_left]
  exact Real.le_norm_self ⟪v.toSpace, w.toSpace⟫_ℝ

lemma ge_sub_norm (v w : ContrMod d) : v.val (Sum.inl 0) * w.val (Sum.inl 0) -
    ‖v.toSpace‖ * ‖w.toSpace‖ ≤ ⟪v, w⟫ₘ := by
  apply le_trans _ (ge_abs_inner_product v w)
  rw [sub_le_sub_iff_left]
  exact norm_inner_le_norm v.toSpace w.toSpace

/-!

# The Minkowski metric and the standard basis

-/

@[simp]
lemma basis_left {v : ContrMod d} (μ : Fin 1 ⊕ Fin d) :
    ⟪ ContrMod.stdBasis μ, v⟫ₘ = η μ μ * v.toFin1dℝ μ := by
  rw [as_sum]
  rcases μ with μ | μ
  · fin_cases μ
    simp only [Fin.zero_eta, Fin.isValue, ContrMod.stdBasis_apply_same, one_mul,
      ContrMod.stdBasis_inl_apply_inr, zero_mul, Finset.sum_const_zero, sub_zero, minkowskiMatrix,
      LieAlgebra.Orthogonal.indefiniteDiagonal, diagonal_apply_eq, Sum.elim_inl]
    rfl
  · simp only [Fin.isValue, ContrMod.stdBasis_apply, reduceCtorEq, ↓reduceIte, zero_mul,
    Sum.inr.injEq, ite_mul, one_mul, Finset.sum_ite_eq, Finset.mem_univ, zero_sub, minkowskiMatrix,
    LieAlgebra.Orthogonal.indefiniteDiagonal, diagonal_apply_eq, Sum.elim_inr, neg_mul, neg_inj]
    rfl

lemma on_basis_mulVec (μ ν : Fin 1 ⊕ Fin d) :
    ⟪ContrMod.stdBasis μ, Λ *ᵥ ContrMod.stdBasis ν⟫ₘ = η μ μ * Λ μ ν := by
  rw [basis_left, ContrMod.mulVec_toFin1dℝ]
  simp [mulVec, dotProduct, ContrMod.stdBasis_apply, ContrMod.toFin1dℝ_eq_val]

lemma on_basis (μ ν : Fin 1 ⊕ Fin d) : ⟪ContrMod.stdBasis μ, ContrMod.stdBasis ν⟫ₘ = η μ ν := by
  trans ⟪ContrMod.stdBasis μ, 1 *ᵥ ContrMod.stdBasis ν⟫ₘ
  · rw [ContrMod.one_mulVec]
  rw [on_basis_mulVec]
  by_cases h : μ = ν
  · subst h
    simp
  · simp only [ne_eq, h, not_false_eq_true, one_apply_ne, mul_zero, off_diag_zero]

lemma matrix_apply_stdBasis (ν μ : Fin 1 ⊕ Fin d) :
    Λ ν μ = η ν ν * ⟪ContrMod.stdBasis ν, Λ *ᵥ ContrMod.stdBasis μ⟫ₘ := by
  rw [on_basis_mulVec, ← mul_assoc]
  simp [η_apply_mul_η_apply_diag ν]

/-!

## Self-adjoint

-/

lemma same_eq_det_toSelfAdjoint (x : ContrMod 3) :
    ⟪x, x⟫ₘ = det (ContrMod.toSelfAdjoint x).1 := by
  rw [ContrMod.toSelfAdjoint_apply_coe, as_sum_toSpace, det_fin_two,
    PauliMatrix.pauliMatrix, PauliMatrix.pauliMatrix, PauliMatrix.pauliMatrix,
    PauliMatrix.pauliMatrix, ContrMod.toSpace,
    ContrMod.toFin1dℝ_eq_val]
  simp only [Fin.isValue, PiLp.inner_apply, Fin.sum_univ_three, ofReal_sub, ofReal_mul, smul_of,
    smul_cons, smul_zero, real_smul, mul_one, smul_empty, smul_neg, Matrix.sub_apply,
    Matrix.smul_apply, one_apply_eq, of_apply, cons_val', cons_val_zero, cons_val_fin_one, sub_zero,
    cons_val_one, sub_neg_eq_add, ne_eq, zero_ne_one, not_false_eq_true, one_apply_ne, zero_sub,
    one_ne_zero]
  ring_nf
  simp only [Fin.isValue, Function.comp_apply, inner_self_eq_norm_sq_to_K, Real.norm_eq_abs,
    RCLike.ofReal_real_eq_id, id_eq, sq_abs, ofReal_add, ofReal_pow, I_sq, mul_neg, mul_one]
  ring

end contrContrContractField

/-!

## The contraction on the basis

-/

lemma contrCoContract_basis {d : ℕ} (i j : Fin 1 ⊕ Fin d) :
    contrCoContract (contrBasis d i ⊗ₜ coBasis d j) = if i = j then (1 : ℝ) else 0 := by
  rw [contrCoContract_hom_tmul]
  simp only [contrBasis_toFin1dℝ, coBasis_toFin1dℝ, dotProduct_single, mul_one]
  rw [Pi.single_apply]
  congr 1
  simp [eq_comm]

lemma coContrContract_basis {d : ℕ} (i j : Fin 1 ⊕ Fin d) :
    coContrContract (coBasis d i ⊗ₜ[ℝ] contrBasis d j) = if i = j then (1 : ℝ) else 0 := by
  rw [coContrContract_hom_tmul]
  simp only [coBasis_toFin1dℝ, contrBasis_toFin1dℝ, dotProduct_single, mul_one]
  rw [Pi.single_apply]
  congr 1
  simp [eq_comm]

end Lorentz
end
