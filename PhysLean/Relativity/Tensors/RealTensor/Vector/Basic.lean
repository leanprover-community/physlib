/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Joseph Tooby-Smith
-/
import PhysLean.Relativity.Tensors.RealTensor.Metrics.Basic
import PhysLean.Relativity.Tensors.Elab
import Mathlib.Geometry.Manifold.IsManifold.Basic
/-!

# Lorentz Vectors

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
def Vector (d : ℕ := 3) := Fin 1 ⊕ Fin d → ℝ

namespace Vector

open TensorSpecies
open Tensor

instance {d} : AddCommMonoid (Vector d) :=
  inferInstanceAs (AddCommMonoid (Fin 1 ⊕ Fin d → ℝ))

instance {d} : Module ℝ (Vector d) :=
  inferInstanceAs (Module ℝ (Fin 1 ⊕ Fin d → ℝ))

instance {d} : AddCommGroup (Vector d) :=
  inferInstanceAs (AddCommGroup (Fin 1 ⊕ Fin d → ℝ))

instance {d} : FiniteDimensional ℝ (Vector d) :=
  inferInstanceAs (FiniteDimensional ℝ (Fin 1 ⊕ Fin d → ℝ))

/-- The equivalence between `Vector d` and `EuclideanSpace ℝ (Fin 1 ⊕ Fin d)`. -/
def equivEuclid (d : ℕ) :
    Vector d ≃ₗ[ℝ] EuclideanSpace ℝ (Fin 1 ⊕ Fin d) :=
  (WithLp.linearEquiv _ _ _).symm

@[simp]
lemma equivEuclid_apply (d : ℕ) (v : Vector d) (i : Fin 1 ⊕ Fin d) :
    equivEuclid d v i = v i := rfl

instance (d : ℕ) : Norm (Vector d) where
  norm := fun v => ‖equivEuclid d v‖

lemma norm_eq_equivEuclid (d : ℕ) (v : Vector d) :
    ‖v‖ = ‖equivEuclid d v‖ := rfl

@[simp]
lemma abs_component_le_norm {d : ℕ} (v : Vector d) (i : Fin 1 ⊕ Fin d) :
    |v i| ≤ ‖v‖ := by
  simp [norm_eq_equivEuclid, PiLp.norm_eq_of_L2, -Fintype.sum_sum_type]
  refine Real.abs_le_sqrt ?_
  trans ∑ j ∈ {i}, (v j) ^ 2
  · simp
  refine Finset.sum_le_univ_sum_of_nonneg (fun i => by positivity)

instance isNormedAddCommGroup (d : ℕ) : NormedAddCommGroup (Vector d) where
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

instance isNormedSpace (d : ℕ) : NormedSpace ℝ (Vector d) where
  norm_smul_le c v := by
    simp only [norm_eq_equivEuclid, map_smul]
    exact norm_smul_le c (equivEuclid d v)
open InnerProductSpace

instance (d : ℕ) : Inner ℝ (Vector d) where
  inner := fun v w => ⟪equivEuclid d v, equivEuclid d w⟫_ℝ

lemma inner_eq_equivEuclid (d : ℕ) (v w : Vector d) :
    ⟪v, w⟫_ℝ = ⟪equivEuclid d v, equivEuclid d w⟫_ℝ := rfl

/-- The Euclidean inner product structure on `CoVector`. -/
instance innerProductSpace (d : ℕ) : InnerProductSpace ℝ (Vector d) where
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
instance : ChartedSpace (Vector d) (Vector d) := chartedSpaceSelf (Vector d)

instance {d} : CoeFun (Vector d) (fun _ => Fin 1 ⊕ Fin d → ℝ) where
  coe := fun v => v

@[simp]
lemma apply_smul {d : ℕ} (c : ℝ) (v : Vector d) (i : Fin 1 ⊕ Fin d) :
    (c • v) i = c * v i := rfl

@[simp]
lemma apply_add {d : ℕ} (v w : Vector d) (i : Fin 1 ⊕ Fin d) :
    (v + w) i = v i + w i := rfl

@[simp]
lemma apply_sub {d : ℕ} (v w : Vector d) (i : Fin 1 ⊕ Fin d) :
    (v - w) i = v i - w i := by rfl

lemma apply_sum {d : ℕ} {ι : Type} [Fintype ι] (f : ι → Vector d) (i : Fin 1 ⊕ Fin d) :
    (∑ j, f j) i = ∑ j, f j i := by
  let P (ι : Type) [Fintype ι] := ∀ (f : ι → Vector d) (i : Fin 1 ⊕ Fin d),
    (∑ j : ι, f j) i = ∑ j, f j i
  revert i f
  change P ι
  apply Fintype.induction_empty_option
  · intro ι1 ι2 _ e h1
    dsimp [P]
    intro f i
    have h' := h1 (f ∘ e) i
    simp at h'
    rw [← @e.sum_comp, ← @e.sum_comp, h']
  · intro f i
    simp only [Finset.univ_eq_empty, Finset.sum_empty]
    rfl
  · intro ι _ h f i
    rw [Fintype.sum_option, apply_add, h, Fintype.sum_option]

@[simp]
lemma neg_apply {d : ℕ} (v : Vector d) (i : Fin 1 ⊕ Fin d) :
    (-v) i = - v i := rfl

@[simp]
lemma zero_apply {d : ℕ} (i : Fin 1 ⊕ Fin d) :
    (0 : Vector d) i = 0 := rfl

/-- The continuous linear map from a Lorentz vector to one of its coordinates. -/
def coordCLM {d : ℕ} (i : Fin 1 ⊕ Fin d) : Vector d →L[ℝ] ℝ := LinearMap.toContinuousLinearMap {
  toFun v := v i
  map_add' := by simp
  map_smul' := by simp}

lemma coordCLM_apply {d : ℕ} (i : Fin 1 ⊕ Fin d) (v : Vector d) :
    coordCLM i v = v i := rfl

@[fun_prop]
lemma coord_continuous {d : ℕ} (i : Fin 1 ⊕ Fin d) :
    Continuous (fun v : Vector d => v i) :=
  (coordCLM i).continuous

@[fun_prop]
lemma coord_contDiff {n} {d : ℕ} (i : Fin 1 ⊕ Fin d) :
    ContDiff ℝ n (fun v : Vector d => v i) :=
  (coordCLM i).contDiff

@[fun_prop]
lemma coord_differentiable {d : ℕ} (i : Fin 1 ⊕ Fin d) :
    Differentiable ℝ (fun v : Vector d => v i) :=
  (coordCLM i).differentiable

@[fun_prop]
lemma coord_differentiableAt {d : ℕ} (i : Fin 1 ⊕ Fin d) (v : Vector d) :
    DifferentiableAt ℝ (fun v : Vector d => v i) v :=
  (coordCLM i).differentiableAt

/-- The continuous linear equivalence between `Vector d` and Euclidean space. -/
def euclidCLE (d : ℕ) : Vector d ≃L[ℝ] EuclideanSpace ℝ (Fin 1 ⊕ Fin d) :=
  LinearEquiv.toContinuousLinearEquiv (equivEuclid d)

/-- The continuous linear equivalence between `Vector d` and the corresponding `Pi` type. -/
def equivPi (d : ℕ) :
    Vector d ≃L[ℝ] Π (_ : Fin 1 ⊕ Fin d), ℝ :=
  LinearEquiv.toContinuousLinearEquiv (LinearEquiv.refl _ _)

@[simp]
lemma equivPi_apply {d : ℕ} (v : Vector d) (i : Fin 1 ⊕ Fin d) :
    equivPi d v i = v i := rfl

@[fun_prop]
lemma continuous_of_apply {d : ℕ} {α : Type*} [TopologicalSpace α]
    (f : α → Vector d)
    (h : ∀ i : Fin 1 ⊕ Fin d, Continuous (fun x => f x i)) :
    Continuous f := by
  rw [← (equivPi d).comp_continuous_iff]
  apply continuous_pi
  intro i
  simp only [Function.comp_apply, equivPi_apply]
  fun_prop

lemma differentiable_apply {d : ℕ} {α : Type*} [NormedAddCommGroup α] [NormedSpace ℝ α]
    (f : α → Vector d) :
    (∀ i : Fin 1 ⊕ Fin d, Differentiable ℝ (fun x => f x i)) ↔ Differentiable ℝ f := by
  apply Iff.intro
  · intro h
    rw [← (Lorentz.Vector.equivPi d).comp_differentiable_iff]
    exact differentiable_pi'' h
  · intro h ν
    change Differentiable ℝ (Lorentz.Vector.coordCLM ν ∘ f)
    apply Differentiable.comp
    · fun_prop
    · exact h

lemma contDiff_apply {n : WithTop ℕ∞} {d : ℕ} {α : Type*}
    [NormedAddCommGroup α] [NormedSpace ℝ α]
    (f : α → Vector d) :
    (∀ i : Fin 1 ⊕ Fin d, ContDiff ℝ n (fun x => f x i)) ↔ ContDiff ℝ n f := by
  apply Iff.intro
  · intro h
    rw [← (Lorentz.Vector.equivPi d).comp_contDiff_iff]
    apply contDiff_pi'
    intro ν
    exact h ν
  · intro h ν
    change ContDiff ℝ n (Lorentz.Vector.coordCLM ν ∘ f)
    apply ContDiff.comp
    · fun_prop
    · exact h

lemma fderiv_apply {d : ℕ} {α : Type*}
    [NormedAddCommGroup α] [NormedSpace ℝ α]
    (f : α → Vector d) (h : Differentiable ℝ f)
    (x : α) (dt : α) (ν : Fin 1 ⊕ Fin d) :
    fderiv ℝ f x dt ν = fderiv ℝ (fun y => f y ν) x dt := by
  change _ = (fderiv ℝ (Lorentz.Vector.coordCLM ν ∘ f) x) dt
  rw [fderiv_comp _ (by fun_prop) (by fun_prop)]
  simp only [ContinuousLinearMap.fderiv, ContinuousLinearMap.coe_comp', Function.comp_apply]
  rfl

@[simp]
lemma fderiv_coord {d : ℕ} (μ : Fin 1 ⊕ Fin d) (x : Vector d) :
    fderiv ℝ (fun v : Vector d => v μ) x = coordCLM μ := by
  change fderiv ℝ (coordCLM μ) x = coordCLM μ
  simp

/-!

## Tensorial

-/

/-- The equivalence between the type of indices of a Lorentz vector and
  `Fin 1 ⊕ Fin d`. -/
def indexEquiv {d : ℕ} :
    ComponentIdx (S := (realLorentzTensor d)) ![Color.up] ≃ Fin 1 ⊕ Fin d :=
  let e : (ComponentIdx (S := (realLorentzTensor d)) ![Color.up])
    ≃ Fin (1 + d) := {
    toFun := fun f => Fin.cast (by rfl) (f 0)
    invFun := fun x => (fun j => Fin.cast (by simp) x)
    left_inv := fun f => by
      ext j
      fin_cases j
      simp
    right_inv := fun x => by rfl}
  e.trans finSumFinEquiv.symm

instance tensorial {d : ℕ} : Tensorial (realLorentzTensor d) ![.up] (Vector d) where
  toTensor := LinearEquiv.symm <|
    Equiv.toLinearEquiv
    ((Tensor.basis (S := (realLorentzTensor d)) ![.up]).repr.toEquiv.trans <|
  Finsupp.equivFunOnFinite.trans <|
  (Equiv.piCongrLeft' _ indexEquiv))
    { map_add := fun x y => by
        simp [Nat.succ_eq_add_one, Nat.reduceAdd, map_add]
        rfl
      map_smul := fun c x => by
        simp [Nat.succ_eq_add_one, Nat.reduceAdd, _root_.map_smul]
        rfl}

open Tensorial

lemma toTensor_symm_apply {d : ℕ} (p : ℝT[d, .up]) :
    (toTensor (self := tensorial)).symm p =
    (Equiv.piCongrLeft' _ indexEquiv <|
    Finsupp.equivFunOnFinite <|
    (Tensor.basis (S := (realLorentzTensor d)) _).repr p) := rfl

lemma toTensor_symm_pure {d : ℕ} (p : Pure (realLorentzTensor d) ![.up]) (i : Fin 1 ⊕ Fin d) :
    (toTensor (self := tensorial)).symm p.toTensor i =
    ((Lorentz.contrBasisFin d).repr (p 0)) (indexEquiv.symm i 0) := by
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
def basis {d : ℕ} : Basis (Fin 1 ⊕ Fin d) ℝ (Vector d) :=
  Pi.basisFun ℝ _

@[simp]
lemma basis_apply {d : ℕ} (μ ν : Fin 1 ⊕ Fin d) :
    basis μ ν = if μ = ν then 1 else 0 := by
  simp [basis]
  erw [Pi.basisFun_apply, Pi.single_apply]
  congr 1
  exact Lean.Grind.eq_congr' rfl rfl

lemma toTensor_symm_basis {d : ℕ} (μ : Fin 1 ⊕ Fin d) :
    (toTensor (self := tensorial)).symm (Tensor.basis ![Color.up] (indexEquiv.symm μ)) =
    basis μ := by
  rw [Tensor.basis_apply]
  funext i
  rw [toTensor_symm_pure]
  simp [contrBasisFin, Pure.basisVector]
  conv_lhs =>
    enter [1, 2]
    change (contrBasisFin d) (indexEquiv.symm μ 0)
  simp [contrBasisFin, indexEquiv, Finsupp.single_apply]

lemma toTensor_basis_eq_tensor_basis {d : ℕ} (μ : Fin 1 ⊕ Fin d) :
    toTensor (basis μ) = Tensor.basis ![Color.up] (indexEquiv.symm μ) := by
  rw [← toTensor_symm_basis]
  simp

lemma basis_eq_map_tensor_basis {d} : basis =
    ((Tensor.basis
    (S := realLorentzTensor d) ![Color.up]).map toTensor.symm).reindex indexEquiv := by
  ext μ
  rw [← toTensor_symm_basis]
  simp

lemma tensor_basis_map_eq_basis_reindex {d} :
    (Tensor.basis (S := realLorentzTensor d) ![Color.up]).map toTensor.symm =
    basis.reindex indexEquiv.symm := by
  rw [basis_eq_map_tensor_basis]
  ext μ
  simp

lemma tensor_basis_repr_toTensor_apply {d : ℕ} (p : Vector d) (μ : ComponentIdx ![Color.up]) :
    (Tensor.basis ![Color.up]).repr (toTensor p) μ =
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

lemma basis_repr_apply {d : ℕ} (p : Vector d) (μ : Fin 1 ⊕ Fin d) :
    basis.repr p μ = p μ := by
  simp [basis]
  erw [Pi.basisFun_repr]

lemma map_apply_eq_basis_mulVec {d : ℕ} (f : Vector d →ₗ[ℝ] Vector d) (p : Vector d) :
    (f p) = (LinearMap.toMatrix basis basis) f *ᵥ p := by
  exact Eq.symm (LinearMap.toMatrix_mulVec_repr basis basis f p)

lemma sum_basis_eq_zero_iff {d : ℕ} (f : Fin 1 ⊕ Fin d → ℝ) :
    (∑ μ, f μ • basis μ) = 0 ↔ ∀ μ, f μ = 0 := by
  apply Iff.intro
  · intro h
    have h1 := (linearIndependent_iff').mp basis.linearIndependent Finset.univ f h
    intro μ
    exact h1 μ (by simp)
  · intro h
    simp [h]

lemma sum_inl_inr_basis_eq_zero_iff {d : ℕ} (f₀ : ℝ) (f : Fin d → ℝ) :
    f₀ • basis (Sum.inl 0) + (∑ i, f i • basis (Sum.inr i)) = 0 ↔
    f₀ = 0 ∧ ∀ i, f i = 0 := by
  let f' : Fin 1 ⊕ Fin d → ℝ := fun μ =>
    match μ with
    | Sum.inl 0 => f₀
    | Sum.inr i => f i
  have h1 : f₀ • basis (Sum.inl 0) + (∑ i, f i • basis (Sum.inr i))
    = ∑ μ, f' μ • basis μ := by simp [f']
  rw [h1, sum_basis_eq_zero_iff]
  simp [f']

/-!

## The action of the Lorentz group

-/

lemma smul_eq_sum {d : ℕ} (i : Fin 1 ⊕ Fin d) (Λ : LorentzGroup d) (p : Vector d) :
    (Λ • p) i = ∑ j, Λ.1 i j * p j := by
  obtain ⟨p, rfl⟩ := toTensor.symm.surjective p
  rw [smul_toTensor_symm]
  apply induction_on_pure (t := p)
  · intro p
    rw [actionT_pure]
    rw [toTensor_symm_pure]
    conv_lhs =>
      enter [1, 2]
      change Λ.1 *ᵥ (p 0)
    rw [contrBasisFin_repr_apply]
    conv_lhs => simp only [Fin.isValue, Nat.succ_eq_add_one, Nat.reduceAdd, indexEquiv,
      cons_val_zero, Fin.cast_eq_self, Equiv.symm_trans_apply, Equiv.symm_symm,
      Equiv.coe_fn_symm_mk, Equiv.symm_apply_apply, ContrMod.mulVec_val]
    rw [mulVec_eq_sum]
    simp only [Finset.sum_apply]
    congr
    funext j
    simp only [Fin.isValue, Pi.smul_apply, transpose_apply, MulOpposite.smul_eq_mul_unop,
      MulOpposite.unop_op, Nat.succ_eq_add_one, Nat.reduceAdd, mul_eq_mul_left_iff]
    left
    rw [toTensor_symm_pure, contrBasisFin_repr_apply]
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

lemma smul_eq_mulVec {d} (Λ : LorentzGroup d) (p : Vector d) :
    Λ • p = Λ.1 *ᵥ p := by
  funext i
  rw [smul_eq_sum, mulVec_eq_sum]
  simp only [op_smul_eq_smul, Finset.sum_apply, Pi.smul_apply, transpose_apply, smul_eq_mul,
    mul_comm]

lemma smul_add {d : ℕ} (Λ : LorentzGroup d) (p q : Vector d) :
    Λ • (p + q) = Λ • p + Λ • q := by simp

@[simp]
lemma smul_sub {d : ℕ} (Λ : LorentzGroup d) (p q : Vector d) :
    Λ • (p - q) = Λ • p - Λ • q := by
  rw [smul_eq_mulVec, smul_eq_mulVec, smul_eq_mulVec, Matrix.mulVec_sub]

lemma smul_zero {d : ℕ} (Λ : LorentzGroup d) :
    Λ • (0 : Vector d) = 0 := by
  rw [smul_eq_mulVec, Matrix.mulVec_zero]

lemma smul_neg {d : ℕ} (Λ : LorentzGroup d) (p : Vector d) :
    Λ • (-p) = - (Λ • p) := by
  rw [smul_eq_mulVec, smul_eq_mulVec, Matrix.mulVec_neg]

lemma neg_smul {d} (Λ : LorentzGroup d) (p : Vector d) :
    (-Λ) • p = - (Λ • p) := by
  funext i
  rw [smul_eq_sum, neg_apply, smul_eq_sum]
  simp

lemma _root_.LorentzGroup.eq_of_action_vector_eq {d : ℕ}
    {Λ Λ' : LorentzGroup d} (h : ∀ p : Vector d, Λ • p = Λ' • p) :
    Λ = Λ' := by
  apply LorentzGroup.eq_of_mulVec_eq
  simpa only [smul_eq_mulVec] using fun x => h x

/-!

## B. The continuous action of the Lorentz group

-/

/-- The Lorentz action on vectors as a continuous linear map. -/
def actionCLM {d : ℕ} (Λ : LorentzGroup d) :
    Vector d →L[ℝ] Vector d :=
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

lemma actionCLM_apply {d : ℕ} (Λ : LorentzGroup d) (p : Vector d) :
    actionCLM Λ p = Λ • p := rfl

lemma actionCLM_injective {d : ℕ} (Λ : LorentzGroup d) :
    Function.Injective (actionCLM Λ) := by
  intro x1 x2
  simp [actionCLM_apply]

lemma actionCLM_surjective {d : ℕ} (Λ : LorentzGroup d) :
    Function.Surjective (actionCLM Λ) := by
  intro x1
  use (actionCLM Λ⁻¹) x1
  simp [actionCLM_apply]

lemma smul_basis {d : ℕ} (Λ : LorentzGroup d) (μ : Fin 1 ⊕ Fin d) :
    Λ • basis μ = ∑ ν, Λ.1 ν μ • basis ν := by
  funext i
  rw [smul_eq_sum]
  simp only [basis_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
    ↓reduceIte]
  trans ∑ ν, ((Λ.1 ν μ • basis ν) i)
  · simp
  rw [Fintype.sum_apply]

/-!

## C. The Spatial part

-/

/-- Extract spatial components from a Lorentz vector,
    returning them as a vector in Euclidean space. -/
abbrev spatialPart {d : ℕ} (v : Vector d) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 fun i => v (Sum.inr i)

lemma spatialPart_apply_eq_toCoord {d : ℕ} (v : Vector d) (i : Fin d) :
    spatialPart v i = v (Sum.inr i) := rfl

lemma spatialPart_basis_sum_inr {d : ℕ} (i : Fin d) (j : Fin d) :
    spatialPart (basis (Sum.inr i)) j =
      (Finsupp.single (Sum.inr i : Fin 1 ⊕ Fin d) 1) (Sum.inr j) := by
  simp [basis_apply]
  rw [Finsupp.single_apply]
  simp

lemma spatialPart_basis_sum_inl {d : ℕ} (i : Fin d) :
    spatialPart (basis (Sum.inl 0)) i = 0 := by simp

/-- The spatial part of a Lorentz vector as a continuous linear map. -/
def spatialCLM (d : ℕ) : Vector d →L[ℝ] EuclideanSpace ℝ (Fin d) where
  toFun v := WithLp.toLp 2 fun i => v (Sum.inr i)
  map_add' v1 v2 := by rfl
  map_smul' c v := by rfl
  cont := by fun_prop

lemma spatialCLM_apply_eq_spatialPart {d : ℕ} (v : Vector d) (i : Fin d) :
    spatialCLM d v i = spatialPart v i := rfl

@[simp]
lemma spatialCLM_basis_sum_inl {d : ℕ} :
    spatialCLM d (basis (Sum.inl 0)) = 0 := by
  ext i
  exact spatialPart_basis_sum_inl i

@[simp]
lemma spatialCLM_basis_sum_inr {d : ℕ} (i : Fin d) :
    spatialCLM d (basis (Sum.inr i)) = EuclideanSpace.basisFun (Fin d) ℝ i := by
  ext j
  rw [spatialCLM_apply_eq_spatialPart, spatialPart_basis_sum_inr i j]
  simp [Finsupp.single_apply]
  congr 1
  exact Eq.propIntro (fun a => id (Eq.symm a)) fun a => id (Eq.symm a)

/-!

## The Temporal component

-/

/-- Extract time component from a Lorentz vector -/
abbrev timeComponent {d : ℕ} (v : Vector d) : ℝ :=
  v (Sum.inl 0)

lemma timeComponent_basis_sum_inr {d : ℕ} (i : Fin d) :
    timeComponent (basis (Sum.inr i)) = 0 := by simp

lemma timeComponent_basis_sum_inl {d : ℕ} :
    timeComponent (d := d) (basis (Sum.inl 0)) = 1 := by simp

/-- The temporal part of a Lorentz vector as a continuous linear map. -/
def temporalCLM (d : ℕ) : Vector d →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap {
    toFun := fun v => v (Sum.inl 0)
    map_add' := by simp
    map_smul' := by simp}

lemma temporalCLM_apply_eq_timeComponent {d : ℕ} (v : Vector d) :
    temporalCLM d v = timeComponent v := rfl

@[simp]
lemma temporalCLM_basis_sum_inr {d : ℕ} (i : Fin d) :
    temporalCLM d (basis (Sum.inr i)) = 0 := by
  simp [temporalCLM_apply_eq_timeComponent, basis_apply]

@[simp]
lemma temporalCLM_basis_sum_inl {d : ℕ} :
    temporalCLM d (basis (Sum.inl 0)) = 1 := by
  simp [temporalCLM_apply_eq_timeComponent, basis_apply]

/-!

## Smoothness

-/

open Manifold in
/-- The structure of a smooth manifold on Vector . -/
def asSmoothManifold (d : ℕ) : ModelWithCorners ℝ (Vector d) (Vector d) := 𝓘(ℝ, Vector d)

/-!

## Properties of the inner product (note not the Minkowski product)

-/
open InnerProductSpace

lemma basis_inner {d : ℕ} (μ : Fin 1 ⊕ Fin d) (p : Lorentz.Vector d) :
    ⟪Lorentz.Vector.basis μ, p⟫_ℝ = p μ := by
  simp [inner_eq_equivEuclid]
  rw [PiLp.inner_apply]
  simp

lemma inner_basis {d : ℕ} (p : Lorentz.Vector d) (μ : Fin 1 ⊕ Fin d) :
    ⟪p, Lorentz.Vector.basis μ⟫_ℝ = p μ := by
  simp [inner_eq_equivEuclid]
  rw [PiLp.inner_apply]
  simp

end Vector

end Lorentz
