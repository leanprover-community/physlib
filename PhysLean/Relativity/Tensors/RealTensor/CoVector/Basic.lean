/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Joseph Tooby-Smith
-/
import PhysLean.Relativity.Tensors.RealTensor.Metrics.Basic
import Mathlib.Geometry.Manifold.IsManifold.Basic
import PhysLean.Relativity.Tensors.Elab
/-!

# Lorentz co vectors

In this module we define Lorentz vectors as real Lorentz tensors with a single up index.
We create an API around Lorentz vectors to make working with them as easy as possible.

-/
open Module IndexNotation
open CategoryTheory
open MonoidalCategory
open Matrix
open MatrixGroups
open Complex
open TensorProduct
open IndexNotation
open CategoryTheory
noncomputable section

namespace Lorentz
open realLorentzTensor

/-- Real contravariant Lorentz vector. -/
def CoVector (d : ℕ := 3) := Fin 1 ⊕ Fin d → ℝ

namespace CoVector

open TensorSpecies
open Tensor

instance {d} : AddCommMonoid (CoVector d) :=
  inferInstanceAs (AddCommMonoid (Fin 1 ⊕ Fin d → ℝ))

instance {d} : Module ℝ (CoVector d) :=
  inferInstanceAs (Module ℝ (Fin 1 ⊕ Fin d → ℝ))

instance {d} : AddCommGroup (CoVector d) :=
  inferInstanceAs (AddCommGroup (Fin 1 ⊕ Fin d → ℝ))

instance {d} : FiniteDimensional ℝ (CoVector d) :=
  inferInstanceAs (FiniteDimensional ℝ (Fin 1 ⊕ Fin d → ℝ))

/-- The equivalence between `CoVector d` and `EuclideanSpace ℝ (Fin 1 ⊕ Fin d)`. -/
def equivEuclid (d : ℕ) :
    CoVector d ≃ₗ[ℝ] EuclideanSpace ℝ (Fin 1 ⊕ Fin d) :=
  (WithLp.linearEquiv _ _ _).symm

instance (d : ℕ) : Norm (CoVector d) where
  norm := fun v => ‖equivEuclid d v‖

lemma norm_eq_equivEuclid (d : ℕ) (v : CoVector d) :
    ‖v‖ = ‖equivEuclid d v‖ := rfl

instance isNormedAddCommGroup (d : ℕ) : NormedAddCommGroup (CoVector d) where
  dist_self x := by simp [norm_eq_equivEuclid]
  dist_comm x y := by
    simpa [norm_eq_equivEuclid] using dist_comm ((equivEuclid d) x) _
  dist_triangle x y z := by
    simpa [norm_eq_equivEuclid] using dist_triangle
      ((equivEuclid d) x) ((equivEuclid d) y) ((equivEuclid d) z)
  eq_of_dist_eq_zero {x y} := by
    simp only [norm_eq_equivEuclid, map_sub]
    intro h
    apply (equivEuclid d).injective
    exact (eq_of_dist_eq_zero h)

instance isNormedSpace (d : ℕ) : NormedSpace ℝ (CoVector d) where
  norm_smul_le c v := by
    simp only [norm_eq_equivEuclid, map_smul]
    exact norm_smul_le c (equivEuclid d v)
open InnerProductSpace

instance (d : ℕ) : Inner ℝ (CoVector d) where
  inner := fun v w => ⟪equivEuclid d v, equivEuclid d w⟫_ℝ

lemma inner_eq_equivEuclid (d : ℕ) (v w : CoVector d) :
    ⟪v, w⟫_ℝ = ⟪equivEuclid d v, equivEuclid d w⟫_ℝ := rfl
/-- The Euclidean inner product structure on `CoVector`. -/
instance innerProductSpace (d : ℕ) : InnerProductSpace ℝ (CoVector d) where
  norm_sq_eq_re_inner v := by
    simp only [inner_eq_equivEuclid, norm_eq_equivEuclid]
    exact InnerProductSpace.norm_sq_eq_re_inner (equivEuclid d v)
  conj_inner_symm x y := by
    simp only [inner_eq_equivEuclid]
    exact InnerProductSpace.conj_inner_symm (equivEuclid d x) (equivEuclid d y)
  add_left x y z := by
    simp only [inner_eq_equivEuclid, map_add]
    exact InnerProductSpace.add_left (equivEuclid d x) (equivEuclid d y) (equivEuclid d z)
  smul_left x y r := by
    simp only [inner_eq_equivEuclid, map_smul]
    exact InnerProductSpace.smul_left (equivEuclid d x) (equivEuclid d y) r

/-- The instance of a `ChartedSpace` on `Vector d`. -/
instance : ChartedSpace (CoVector d) (CoVector d) := chartedSpaceSelf (CoVector d)

instance {d} : CoeFun (CoVector d) (fun _ => Fin 1 ⊕ Fin d → ℝ) where
  coe := fun v => v

@[simp]
lemma apply_smul {d : ℕ} (c : ℝ) (v : CoVector d) (i : Fin 1 ⊕ Fin d) :
    (c • v) i = c * v i := rfl

@[simp]
lemma apply_add {d : ℕ} (v w : CoVector d) (i : Fin 1 ⊕ Fin d) :
    (v + w) i = v i + w i := rfl

@[simp]
lemma apply_sub {d : ℕ} (v w : CoVector d) (i : Fin 1 ⊕ Fin d) :
    (v - w) i = v i - w i := by rfl

@[simp]
lemma neg_apply {d : ℕ} (v : CoVector d) (i : Fin 1 ⊕ Fin d) :
    (-v) i = - v i := rfl

@[simp]
lemma zero_apply {d : ℕ} (i : Fin 1 ⊕ Fin d) :
    (0 : CoVector d) i = 0 := rfl
/-!

## Tensorial

-/

/-- The equivalence between the type of indices of a Lorentz vector and
  `Fin 1 ⊕ Fin d`. -/
def indexEquiv {d : ℕ} :
    ComponentIdx (S := (realLorentzTensor d)) ![Color.down] ≃ Fin 1 ⊕ Fin d :=
  let e : (ComponentIdx (S := (realLorentzTensor d)) ![Color.down])
    ≃ Fin (1 + d) := {
    toFun := fun f => Fin.cast (by rfl) (f 0)
    invFun := fun x => (fun j => Fin.cast (by simp) x)
    left_inv := fun f => by
      ext j
      fin_cases j
      simp
    right_inv := fun x => by rfl}
  e.trans finSumFinEquiv.symm

instance tensorial {d : ℕ} : Tensorial (realLorentzTensor d) ![.down] (CoVector d) where
  toTensor := LinearEquiv.symm <|
    Equiv.toLinearEquiv
    ((Tensor.basis (S := (realLorentzTensor d)) ![.down]).repr.toEquiv.trans <|
  Finsupp.equivFunOnFinite.trans <|
  (Equiv.piCongrLeft' _ indexEquiv))
    { map_add := fun x y => by
        simp [Nat.succ_eq_add_one, Nat.reduceAdd, map_add]
        rfl
      map_smul := fun c x => by
        simp [Nat.succ_eq_add_one, Nat.reduceAdd, _root_.map_smul]
        rfl}

open Tensorial

lemma toTensor_symm_apply {d : ℕ} (p : ℝT[d, .down]) :
    (toTensor (self := tensorial)).symm p =
    (Equiv.piCongrLeft' _ indexEquiv <|
    Finsupp.equivFunOnFinite <|
    (Tensor.basis (S := (realLorentzTensor d)) _).repr p) := rfl

lemma toTensor_symm_pure {d : ℕ} (p : Pure (realLorentzTensor d) ![.down]) (i : Fin 1 ⊕ Fin d) :
    (toTensor (self := tensorial)).symm p.toTensor i =
    ((Lorentz.coBasisFin d).repr (p 0)) (indexEquiv.symm i 0) := by
  rw [toTensor_symm_apply]
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd,
    Equiv.piCongrLeft'_apply, Finsupp.equivFunOnFinite_apply, Fin.isValue]
  rw [Tensor.basis_repr_pure]
  simp only [Pure.component, Finset.univ_unique, Fin.default_eq_zero, Fin.isValue,
    Finset.prod_singleton, cons_val_zero]
  rfl

/-!

## Basis

-/

/-- The basis on `Vector d` indexed by `Fin 1 ⊕ Fin d`. -/
def basis {d : ℕ} : Basis (Fin 1 ⊕ Fin d) ℝ (CoVector d) :=
  Pi.basisFun ℝ _

@[simp]
lemma basis_apply {d : ℕ} (μ ν : Fin 1 ⊕ Fin d) :
    basis μ ν = if μ = ν then 1 else 0 := by
  simp [basis]
  erw [Pi.basisFun_apply, Pi.single_apply]
  congr 1
  exact Lean.Grind.eq_congr' rfl rfl

lemma toTensor_symm_basis {d : ℕ} (μ : Fin 1 ⊕ Fin d) :
    (toTensor (self := tensorial)).symm (Tensor.basis ![Color.down] (indexEquiv.symm μ)) =
    basis μ := by
  rw [Tensor.basis_apply]
  funext i
  rw [toTensor_symm_pure]
  simp [coBasisFin, Pure.basisVector]
  conv_lhs =>
    enter [1, 2]
    change (coBasisFin d) (indexEquiv.symm μ 0)
  simp [coBasisFin, indexEquiv, Finsupp.single_apply]

lemma toTensor_basis_eq_tensor_basis {d : ℕ} (μ : Fin 1 ⊕ Fin d) :
    toTensor (basis μ) = Tensor.basis ![Color.down] (indexEquiv.symm μ) := by
  rw [← toTensor_symm_basis]
  simp

lemma basis_eq_map_tensor_basis {d} : basis =
    ((Tensor.basis (S := realLorentzTensor d) ![Color.down]).map
    toTensor.symm).reindex indexEquiv := by
  ext μ
  rw [← toTensor_symm_basis]
  simp

lemma tensor_basis_map_eq_basis_reindex {d} :
    (Tensor.basis (S := realLorentzTensor d) ![Color.down]).map toTensor.symm =
    basis.reindex indexEquiv.symm := by
  rw [basis_eq_map_tensor_basis]
  ext μ
  simp

lemma tensor_basis_repr_toTensor_apply {d : ℕ} (p : CoVector d) (μ : ComponentIdx ![Color.down]) :
    (Tensor.basis ![Color.down]).repr (toTensor p) μ =
    p (indexEquiv μ) := by
  obtain ⟨p, rfl⟩ := toTensor.symm.surjective p
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, LinearEquiv.apply_symm_apply]
  apply induction_on_pure (t := p)
  · intro p
    rw [Tensor.basis_repr_pure]
    simp only [Pure.component, Finset.univ_unique, Fin.default_eq_zero, Fin.isValue,
      Finset.prod_singleton, cons_val_zero, Nat.succ_eq_add_one, Nat.reduceAdd]
    rw [toTensor_symm_pure]
    simp
    rfl
  · intro r t h
    simp [h]
  · intro t1 t2 h1 h2
    simp [h1, h2]

lemma basis_repr_apply {d : ℕ} (p : CoVector d) (μ : Fin 1 ⊕ Fin d) :
    basis.repr p μ = p μ := by
  simp [basis]
  erw [Pi.basisFun_repr]

lemma map_apply_eq_basis_mulVec {d : ℕ} (f : CoVector d →ₗ[ℝ] CoVector d) (p : CoVector d) :
    (f p) = (LinearMap.toMatrix basis basis) f *ᵥ p := by
  exact Eq.symm (LinearMap.toMatrix_mulVec_repr basis basis f p)

/-!

## The action of the Lorentz group

-/

lemma smul_eq_sum {d : ℕ} (i : Fin 1 ⊕ Fin d) (Λ : LorentzGroup d) (p : CoVector d) :
    (Λ • p) i = ∑ j, Λ⁻¹.1 j i * p j := by
  obtain ⟨p, rfl⟩ := toTensor.symm.surjective p
  rw [smul_toTensor_symm]
  apply induction_on_pure (t := p)
  · intro p
    rw [actionT_pure]
    rw [toTensor_symm_pure]
    conv_lhs =>
      enter [1, 2]
      change (LorentzGroup.transpose Λ⁻¹) *ᵥ (p 0)
    rw [coBasisFin_repr_apply]
    conv_lhs => simp [indexEquiv]

    rw [mulVec_eq_sum]
    simp only [Finset.sum_apply]
    congr
    funext j
    simp [Fin.isValue, Pi.smul_apply, transpose_apply, MulOpposite.smul_eq_mul_unop,
      MulOpposite.unop_op, Nat.succ_eq_add_one, Nat.reduceAdd]
    congr
    rw [toTensor_symm_pure, coBasisFin_repr_apply]
    congr
    simp [indexEquiv]
  · intro r t h
    simp only [actionT_smul, _root_.map_smul]
    change r * toTensor (self := tensorial).symm (Λ • t) i = _
    rw [h]
    rw [Finset.mul_sum]
    congr
    funext x
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, apply_smul]
    ring
  · intro t1 t2 h1 h2
    simp only [actionT_add, map_add, h1, h2, apply_add]
    rw [← Finset.sum_add_distrib]
    congr
    funext x
    ring

lemma smul_eq_mulVec {d} (Λ : LorentzGroup d) (p : CoVector d) :
    Λ • p = (LorentzGroup.transpose Λ⁻¹).1 *ᵥ p := by
  funext i
  rw [smul_eq_sum, mulVec_eq_sum]
  simp only [op_smul_eq_smul, Finset.sum_apply, Pi.smul_apply, transpose_apply, smul_eq_mul,
    mul_comm]
  rfl

lemma smul_add {d : ℕ} (Λ : LorentzGroup d) (p q : CoVector d) :
    Λ • (p + q) = Λ • p + Λ • q := by simp

@[simp]
lemma smul_sub {d : ℕ} (Λ : LorentzGroup d) (p q : CoVector d) :
    Λ • (p - q) = Λ • p - Λ • q := by
  rw [smul_eq_mulVec, smul_eq_mulVec, smul_eq_mulVec, Matrix.mulVec_sub]

lemma smul_zero {d : ℕ} (Λ : LorentzGroup d) :
    Λ • (0 : CoVector d) = 0 := by
  rw [smul_eq_mulVec, Matrix.mulVec_zero]

lemma smul_neg {d : ℕ} (Λ : LorentzGroup d) (p : CoVector d) :
    Λ • (-p) = - (Λ • p) := by
  rw [smul_eq_mulVec, smul_eq_mulVec, Matrix.mulVec_neg]

/-- The Lorentz action on vectors as a continuous linear map. -/
def actionCLM {d : ℕ} (Λ : LorentzGroup d) :
    CoVector d →L[ℝ] CoVector d :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => Λ • v
      map_add' := smul_add Λ
      map_smul' := fun c v => by
        simp only [Nat.succ_eq_add_one, Nat.reduceAdd, RingHom.id_apply]
        funext i
        simp [smul_eq_sum]
        ring_nf
        congr
        rw [Finset.mul_sum]
        congr
        funext j
        ring}

lemma actionCLM_apply {d : ℕ} (Λ : LorentzGroup d) (p : CoVector d) :
    actionCLM Λ p = Λ • p := rfl

lemma smul_basis {d : ℕ} (Λ : LorentzGroup d) (μ : Fin 1 ⊕ Fin d) :
    Λ • basis μ = ∑ ν, Λ⁻¹.1 μ ν • basis ν := by
  funext i
  rw [smul_eq_sum]
  simp only [basis_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
    ↓reduceIte]
  trans ∑ ν, ((Λ⁻¹.1 μ ν • basis ν) i)
  · simp
  rw [Fintype.sum_apply]

end CoVector

end Lorentz
