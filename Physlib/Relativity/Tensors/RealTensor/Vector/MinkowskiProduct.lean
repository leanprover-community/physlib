/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.Tensors.RealTensor.Vector.Tensorial
public import Physlib.Relativity.Tensors.RealTensor.Metrics.Basic
/-!

# Minkowski product on Lorentz vectors

In this module we define and create an API around the Minkowski product on Lorentz vectors.

-/

@[expose] public section

open Module
open Matrix
open MatrixGroups
noncomputable section

namespace Lorentz
open realLorentzTensor

namespace Vector

open TensorSpecies
open Tensor

/-!

# The minkowskiProduct

-/

/-- The Minkowski product of Lorentz vectors in the +--- convention.. -/
def minkowskiProductMap {d : ℕ} (p q : Vector d) : ℝ :=
  {η' d | μ ν ⊗ p | μ ⊗ q | ν}ᵀ.toScalar

lemma minkowskiProductMap_toCoord {d : ℕ} (p q : Vector d) :
    minkowskiProductMap p q = p (Sum.inl 0) * q (Sum.inl 0) -
    ∑ i, p (Sum.inr i) * q (Sum.inr i) := by
  dsimp only [minkowskiProductMap, Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue]
  rw [toScalar_eq_repr, contrT_basis_repr_apply_eq_fin]
  conv_lhs =>
    enter [2, x]
    rw [prodT_basis_repr_apply, contrT_basis_repr_apply_eq_fin]
    enter [1, 2, y]
    rw [prodT_basis_repr_apply]
    enter [1]
    erw [coMetric_repr_apply_eq_minkowskiMatrix]
  simp only [tensor_basis_repr_toTensor_apply]
  change ∑ x, (∑ y, minkowskiMatrix y x * p y) * q x = _
  conv_lhs =>
    enter [2, x, 1]
    rw [Finset.sum_eq_single x
      (fun y _ h => by rw [minkowskiMatrix.off_diag_zero h, zero_mul]) (by simp)]
  simp only [Fintype.sum_sum_type, Finset.univ_unique, Fin.default_eq_zero,
    Finset.sum_singleton, minkowskiMatrix.inl_0_inl_0, one_mul, minkowskiMatrix.inr_i_inr_i,
    neg_mul, Finset.sum_neg_distrib]
  ring

lemma minkowskiProductMap_symm {d : ℕ} (p q : Vector d) :
    minkowskiProductMap p q = minkowskiProductMap q p := by
  simp only [minkowskiProductMap_toCoord, mul_comm]

@[simp]
lemma minkowskiProductMap_add_fst {d : ℕ} (p q r : Vector d) :
    minkowskiProductMap (p + q) r = minkowskiProductMap p r + minkowskiProductMap q r := by
  simp only [minkowskiProductMap_toCoord, apply_add, add_mul, Finset.sum_add_distrib]
  ring

@[simp]
lemma minkowskiProductMap_add_snd {d : ℕ} (p q r : Vector d) :
    minkowskiProductMap p (q + r) = minkowskiProductMap p q + minkowskiProductMap p r := by
  rw [minkowskiProductMap_symm, minkowskiProductMap_add_fst]
  rw [minkowskiProductMap_symm q p, minkowskiProductMap_symm r p]

@[simp]
lemma minkowskiProductMap_smul_fst {d : ℕ} (c : ℝ) (p q : Vector d) :
    minkowskiProductMap (c • p) q = c * minkowskiProductMap p q := by
  simp only [minkowskiProductMap_toCoord, apply_smul, mul_sub, Finset.mul_sum, mul_assoc]

@[simp]
lemma minkowskiProductMap_smul_snd {d : ℕ} (c : ℝ) (p q : Vector d) :
    minkowskiProductMap p (c • q) = c * minkowskiProductMap p q := by
  rw [minkowskiProductMap_symm, minkowskiProductMap_smul_fst, minkowskiProductMap_symm q p]

/-- The Minkowski product of two Lorentz vectors as a linear map. -/
def minkowskiProduct {d : ℕ} : Vector d →L[ℝ] Vector d →L[ℝ] ℝ where
  toFun p := {
    toFun := fun q => minkowskiProductMap p q
    map_add' := fun q r => by
      simp
    map_smul' := fun c q => by
      simp
    cont := by
      conv =>
        enter [1, q]
        rw [minkowskiProductMap_toCoord]
      fun_prop
  }
  map_add' := fun p r => by
    apply ContinuousLinearMap.ext
    intro x
    simp
  map_smul' := fun c p => by
    apply ContinuousLinearMap.ext
    intro x
    simp
  cont := by
    rw [continuous_clm_apply]
    intro q
    simp only [ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk]
    conv =>
        enter [1, p]
        rw [minkowskiProductMap_toCoord]
    fun_prop

@[inherit_doc minkowskiProduct]
scoped notation "⟪" p ", " q "⟫ₘ" => minkowskiProduct p q

lemma minkowskiProduct_apply {d : ℕ} (p q : Vector d) :
    ⟪p, q⟫ₘ = minkowskiProductMap p q := rfl

lemma minkowskiProduct_symm {d : ℕ} (p q : Vector d) :
    ⟪p, q⟫ₘ = ⟪q, p⟫ₘ := by
  rw [minkowskiProduct_apply, minkowskiProductMap_symm]
  rfl

lemma minkowskiProduct_toCoord {d : ℕ} (p q : Vector d) :
    ⟪p, q⟫ₘ = p (Sum.inl 0) * q (Sum.inl 0) - ∑ i, p (Sum.inr i) * q (Sum.inr i) := by
  rw [minkowskiProduct_apply, minkowskiProductMap_toCoord]

lemma minkowskiProduct_toCoord_minkowskiMatrix {d : ℕ} (p q : Vector d) :
    ⟪p, q⟫ₘ = ∑ μ, minkowskiMatrix μ μ * p μ * q μ := by
  rw [minkowskiProduct_toCoord]
  simp only [Fin.isValue, Fintype.sum_sum_type, Finset.univ_unique, Fin.default_eq_zero,
    Finset.sum_singleton, minkowskiMatrix.inl_0_inl_0, one_mul, minkowskiMatrix.inr_i_inr_i,
    neg_mul, Finset.sum_neg_distrib]
  rfl

@[simp]
lemma minkowskiProduct_invariant {d : ℕ} (p q : Vector d) (Λ : LorentzGroup d) :
    ⟪Λ • p, Λ • q⟫ₘ = ⟪p, q⟫ₘ := by
  rw [minkowskiProduct_apply, minkowskiProductMap, ← actionT_coMetric Λ]
  simp only [Tensorial.toTensor_smul]
  rw [prodT_equivariant, contrT_equivariant, prodT_equivariant, contrT_equivariant,
    toScalar_equivariant]
  rfl

open InnerProductSpace in
lemma minkowskiProduct_eq_timeComponent_spatialPart {d : ℕ} (p q : Vector d) :
    ⟪p, q⟫ₘ = p.timeComponent * q.timeComponent -
      ⟪p.spatialPart, q.spatialPart⟫_ℝ := by
  rw [minkowskiProduct_toCoord]
  simp [PiLp.inner_apply, conj_trivial, mul_comm]

lemma minkowskiProduct_self_eq_timeComponent_spatialPart {d : ℕ} (p : Vector d) :
    ⟪p, p⟫ₘ = ‖p.timeComponent‖ ^ 2 - ‖p.spatialPart‖ ^ 2 := by
  rw [minkowskiProduct_eq_timeComponent_spatialPart]
  congr 1
  · rw [@RCLike.norm_sq_eq_def_ax]
    simp
  · exact real_inner_self_eq_norm_sq p.spatialPart

lemma minkowskiProduct_self_le_timeComponent_sq {d : ℕ} (p : Vector d) :
    ⟪p, p⟫ₘ ≤ p.timeComponent ^ 2 := by
  rw [minkowskiProduct_self_eq_timeComponent_spatialPart]
  simp

/-- `⟪u, u⟫ₘ = (u⁰)² - ‖u_spatial‖²`. -/
lemma minkowskiProduct_self_eq_sq_sub {d : ℕ} (u : Vector d) :
    ⟪u, u⟫ₘ = u.timeComponent ^ 2 - ‖u.spatialPart‖ ^ 2 := by
  rw [minkowskiProduct_self_eq_timeComponent_spatialPart, Real.norm_eq_abs, sq_abs]

/-- `⟪u + v, u + v⟫ₘ = ⟪u, u⟫ₘ + 2 ⟪u, v⟫ₘ + ⟪v, v⟫ₘ`. -/
lemma minkowskiProduct_add_self {d : ℕ} (u v : Vector d) :
    ⟪u + v, u + v⟫ₘ = ⟪u, u⟫ₘ + 2 * ⟪u, v⟫ₘ + ⟪v, v⟫ₘ := by
  simp only [map_add, _root_.add_apply]
  rw [minkowskiProduct_symm v u]
  ring

/-- `⟪μ • u, μ • u⟫ₘ = μ² ⟪u, u⟫ₘ`. -/
lemma minkowskiProduct_smul_self {d : ℕ} (μ : ℝ) (u : Vector d) :
    ⟪μ • u, μ • u⟫ₘ = μ ^ 2 * ⟪u, u⟫ₘ := by
  simp only [map_smul, _root_.smul_apply, smul_eq_mul]
  ring

/-- `√⟪μ • u, μ • u⟫ₘ = μ √⟪u, u⟫ₘ` for `μ ≥ 0`. -/
lemma sqrt_minkowskiProduct_smul_self {d : ℕ} {μ : ℝ} (hμ : 0 ≤ μ) (u : Vector d) :
    √⟪μ • u, μ • u⟫ₘ = μ * √⟪u, u⟫ₘ := by
  rw [minkowskiProduct_smul_self, Real.sqrt_mul (sq_nonneg μ), Real.sqrt_sq hμ]

@[simp]
lemma minkowskiProduct_basis_left {d : ℕ} (μ : Fin 1 ⊕ Fin d) (p : Vector d) :
    ⟪basis μ, p⟫ₘ = minkowskiMatrix μ μ * p μ := by
  rw [minkowskiProduct_toCoord_minkowskiMatrix]
  simp

@[simp]
lemma minkowskiProduct_basis_right {d : ℕ} (μ : Fin 1 ⊕ Fin d) (p : Vector d) :
    ⟪p, basis μ⟫ₘ = minkowskiMatrix μ μ * p μ := by
  rw [minkowskiProduct_symm, minkowskiProduct_basis_left]

@[simp]
lemma minkowskiProduct_eq_zero_forall_iff {d : ℕ} (p : Vector d) :
    (∀ q : Vector d, ⟪p, q⟫ₘ = 0) ↔ p = 0 := by
  constructor
  · intro h
    funext μ
    rw [← minkowskiMatrix.mul_η_diag_eq_iff (μ := μ), ← minkowskiProduct_basis_right, h (basis μ)]
    simp
  · intro h
    subst h
    simp

/-!

## The adjoint of a linear map

-/

lemma map_minkowskiProduct_eq_self_forall_iff {d : ℕ} (f : Vector d →ₗ[ℝ] Vector d) :
    (∀ p q : Vector d, ⟪f p, q⟫ₘ = ⟪p, q⟫ₘ) ↔ f = LinearMap.id := by
  constructor
  · intro h
    ext1 p
    have h1 := h p
    have h2 : ∀ q, ⟪f p - p, q⟫ₘ = 0 := by
      intro q
      simp [h1 q]
    rw [minkowskiProduct_eq_zero_forall_iff] at h2
    simp only [LinearMap.id_coe, id_eq]
    rw [sub_eq_zero] at h2
    exact h2
  · intro h
    subst h
    simp

/-- The adjoint of a linear map from `Vector d` to itself with respect to
  the `minkowskiProduct`. -/
def adjoint {d : ℕ} (f : Vector d →ₗ[ℝ] Vector d) : Vector d →ₗ[ℝ] Vector d :=
  (LinearMap.toMatrix Vector.basis Vector.basis).symm <|
  minkowskiMatrix.dual <|
  LinearMap.toMatrix Vector.basis Vector.basis f

lemma map_minkowskiProduct_eq_adjoint {d : ℕ} (f : Vector d →ₗ[ℝ] Vector d) (p q : Vector d) :
    ⟪f p, q⟫ₘ = ⟪p, adjoint f q⟫ₘ := by
  rw [minkowskiProduct_toCoord_minkowskiMatrix, minkowskiProduct_toCoord_minkowskiMatrix]
  simp only [map_apply_eq_basis_mulVec, adjoint, LinearMap.toMatrix_symm,
    LinearMap.toMatrix_toLin, mulVec_eq_sum, op_smul_eq_smul, Finset.sum_apply, Pi.smul_apply,
    transpose_apply, smul_eq_mul, minkowskiMatrix.dual_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => ?_
  ring_nf
  rw [minkowskiMatrix.η_apply_sq_eq_one]
  ring

lemma minkowskiProduct_map_eq_adjoint {d : ℕ} (f : Vector d →ₗ[ℝ] Vector d) (p q : Vector d) :
    ⟪p, f q⟫ₘ = ⟪adjoint f p, q⟫ₘ := by
  rw [minkowskiProduct_symm, map_minkowskiProduct_eq_adjoint f q p,
    minkowskiProduct_symm]

/-!

## The property `IsLorentz` of linear maps

-/

/-- A linear map `Vector d →ₗ[ℝ] Vector d` satisfies `IsLorentz` if it preserves
  the minkowski product. -/
def IsLorentz {d : ℕ} (f : Vector d →ₗ[ℝ] Vector d) :
    Prop := ∀ p q : Vector d, ⟪f p, f q⟫ₘ = ⟪p, q⟫ₘ

lemma isLorentz_iff {d : ℕ} (f : Vector d →ₗ[ℝ] Vector d) :
    IsLorentz f ↔ ∀ p q : Vector d, ⟪f p, f q⟫ₘ = ⟪p, q⟫ₘ := by
  rfl

lemma isLorentz_iff_basis {d : ℕ} (f : Vector d →ₗ[ℝ] Vector d) :
    IsLorentz f ↔ ∀ μ ν : Fin 1 ⊕ Fin d, ⟪f (basis μ), f (basis ν)⟫ₘ = ⟪basis μ, basis ν⟫ₘ := by
  rw [isLorentz_iff]
  constructor
  · exact fun a μ ν => a (basis μ) (basis ν)
  intro h p q
  have hp : p = ∑ μ, p μ • basis μ := (Basis.sum_repr basis p).symm
  have hq : q = ∑ ν, q ν • basis ν := (Basis.sum_repr basis q).symm
  rw [hp, hq]
  simp [- Fintype.sum_sum_type, h]

lemma isLorentz_iff_comp_adjoint_eq_id {d : ℕ} (f : Vector d →ₗ[ℝ] Vector d) :
    IsLorentz f ↔ adjoint f ∘ₗ f = LinearMap.id := by
  rw [isLorentz_iff]
  conv_lhs =>
    enter [p, q]
    rw [minkowskiProduct_map_eq_adjoint]
  change (∀ (p q : Vector d), (minkowskiProduct ((adjoint f ∘ₗ f) p)) q =
    (minkowskiProduct p) q) ↔ _
  rw [map_minkowskiProduct_eq_self_forall_iff]

lemma isLorentz_iff_toMatrix_mem_lorentzGroup {d : ℕ} (f : Vector d →ₗ[ℝ] Vector d) :
    IsLorentz f ↔ LinearMap.toMatrix Vector.basis Vector.basis f ∈ LorentzGroup d := by
  rw [isLorentz_iff_comp_adjoint_eq_id]
  rw [LorentzGroup.mem_iff_dual_mul_self]
  trans LinearMap.toMatrix Vector.basis Vector.basis (adjoint f ∘ₗ f) =
    LinearMap.toMatrix Vector.basis Vector.basis (LinearMap.id : Vector d →ₗ[ℝ] Vector d)
  · exact Iff.symm (EmbeddingLike.apply_eq_iff_eq (LinearMap.toMatrix basis basis))
  simp only [LinearMap.toMatrix_id_eq_basis_toMatrix, Basis.toMatrix_self]
  rw [LinearMap.toMatrix_comp Vector.basis Vector.basis]
  simp [adjoint]

end Vector

end Lorentz
