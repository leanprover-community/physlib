/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhi Kai Pong, Joseph Tooby-Smith, Lode Vermeulen
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Physlib.Mathematics.Distribution.Basic
public import Physlib.Relativity.Tensors.RealTensor.Vector.Basic
public import Physlib.SpaceAndTime.Space.Module
public import Mathlib.Analysis.InnerProductSpace.Calculus
/-!

# Derivatives on Space

## i. Overview

In this module we define derivatives of functions and distributions on space `Space d`,
in the standard directions.

## ii. Key results

- `deriv` : The derivative of a function on space in a given direction.
- `distDeriv` : The derivative of a distribution on space in a given direction.

## iii. Table of contents

- A. Derivatives of functions on `Space d`
  - A.1. Basic equalities
  - A.2. Derivative of the constant function
  - A.3. Derivative distributes over addition
  - A.4. Derivative distributes over scalar multiplication
  - A.5. Two spatial derivatives commute
  - A.6. Derivative of a component
  - A.7. Derivative of a component squared
  - A.8. Derivivatives of components
  - A.9. Derivative of a norm squared
    - A.9.1. Differentiability of the norm squared function
    - A.9.2. Derivative of the norm squared function
  - A.10. Derivative of the inner product
    - A.10.1. Differentiability of the inner product function
    - A.10.2. Derivative of the inner product function
    - A.10.3. Derivative of the inner product on one side
  - A.11. Differentiability of derivatives
- B. Derivatives of distributions on `Space d`
  - B.1. The definition
  - B.2. Basic equality
  - B.3. Commutation of derivatives

## iv. References

* None.
-/

@[expose] public section

open Physlib

namespace Space

/-!

## A. Derivatives of functions on `Space d`

-/

/-- Given a function `f : Space d → M` the derivative of `f` in direction `μ`. -/
noncomputable def deriv {M d} [AddCommGroup M] [Module ℝ M] [TopologicalSpace M]
    (μ : Fin d) (f : Space d → M) : Space d → M :=
  (fun x => fderiv ℝ f x (basis μ))

@[inherit_doc deriv]
macro "∂[" i:term "]" : term => `(deriv $i)

/-!

### A.1. Basic equalities

-/

lemma deriv_eq [AddCommGroup M] [Module ℝ M] [TopologicalSpace M]
    (μ : Fin d) (f : Space d → M) (x : Space d) :
    deriv μ f x = fderiv ℝ f x (basis μ) := by rfl

lemma deriv_eq_fderiv_fun [AddCommGroup M] [Module ℝ M] [TopologicalSpace M]
    (μ : Fin d) (f : Space d → M) :
    deriv μ f = fun x => fderiv ℝ (fun x => f x) x (basis μ) := by rfl

lemma deriv_eq_fderiv_basis [AddCommGroup M] [Module ℝ M] [TopologicalSpace M]
    (μ : Fin d) (f : Space d → M) (x : Space d) :
    deriv μ f x = fderiv ℝ f x (basis μ) := by rfl

lemma fderiv_eq_sum_deriv {M d} [AddCommGroup M] [Module ℝ M] [TopologicalSpace M]
    (f : Space d → M) (x y : Space d) :
    fderiv ℝ f x y = ∑ i : Fin d, y i • ∂[i] f x := by
  conv_lhs => rw [← basis.sum_repr y]
  simp [deriv_eq_fderiv_basis]

open Manifold in
/-- The spatial-derivative in terms of the derivative of functions between
  manifolds. -/
lemma deriv_eq_mfderiv {M d} [NormedAddCommGroup M] [NormedSpace ℝ M]
    (μ : Fin d) (f : Space d → M) (x : Space d) :
    deriv μ f x = mfderiv 𝓘(ℝ, Space d) 𝓘(ℝ, M) f x (basis μ) := by
  rw [deriv_eq_fderiv_basis, ← mfderiv_eq_fderiv]
  rfl

open Manifold in
lemma mdifferentiable_manifoldStructure_iff_differentiable {M d} [NormedAddCommGroup M]
    [NormedSpace ℝ M] {f : Space d → M} {x : Space d} :
    MDifferentiableAt (𝓡 d) 𝓘(ℝ, M) f x ↔ DifferentiableAt ℝ f x := by
  refine ⟨fun h => mdifferentiableAt_iff_differentiableAt.mp <| h.comp (I' := 𝓡 d) x
    (modelDiffeo.symm.mdifferentiable WithTop.top_ne_zero).mdifferentiableAt,
    fun h => (mdifferentiableAt_iff_differentiableAt.mpr h).comp (I' := 𝓘(ℝ, Space d)) x
      (modelDiffeo.mdifferentiable WithTop.top_ne_zero).mdifferentiableAt⟩

TODO "Make the version of the derivative described through
  `deriv_eq_mfderiv_manifoldStructure` the definition of `deriv` and prove the
  equivalence with the current definition, under suitable conditions."

open Manifold in
set_option backward.isDefEq.respectTransparency false in
/-- The spatial-derivative in terms of the derivative of functions between
  manifolds with the manifold structure `Space.manifoldStructure d`. -/
lemma deriv_eq_mfderiv_manifoldStructure {M d} [NormedAddCommGroup M] [NormedSpace ℝ M]
    (μ : Fin d) (f : Space d → M) (x : Space d) :
    deriv μ f x = mfderiv (𝓡 d) 𝓘(ℝ, M) f x (EuclideanSpace.single μ 1) := by
  by_cases hf : DifferentiableAt ℝ f x
  · rw [deriv_eq_mfderiv]
    change _ = mfderiv (𝓡 d) 𝓘(ℝ, M)
      (f ∘ modelDiffeo) x (EuclideanSpace.single μ 1)
    rw [mfderiv_comp (I' := 𝓘(ℝ, Space d)) _ hf.mdifferentiableAt
      (modelDiffeo.mdifferentiable WithTop.top_ne_zero).mdifferentiableAt]
    simp only [Function.comp_apply, modelDiffeo_apply, mfderiv_eq_fderiv,
      ContinuousLinearMap.coe_comp]
    rw [basis_eq_mfderiv_modelDiffeo_single]
    rfl
  · rw [deriv_eq, fderiv_zero_of_not_differentiableAt hf,
      mfderiv_zero_of_not_mdifferentiableAt <|
      mdifferentiable_manifoldStructure_iff_differentiable.mp.mt hf]
    simp

/-!

### A.2. Derivative of the constant function

-/

@[simp]
lemma deriv_const [NormedAddCommGroup M] [NormedSpace ℝ M] (m : M) (μ : Fin d) :
    deriv μ (fun _ => m) t = 0 := by
  simp [deriv]

/-!

### A.3. Derivative distributes over addition and subtraction

-/

/-- Derivatives on space distribute over addition. -/
@[to_fun]
lemma deriv_add [NormedAddCommGroup M] [NormedSpace ℝ M]
    (f1 f2 : Space d → M) (hf1 : Differentiable ℝ f1) (hf2 : Differentiable ℝ f2) :
    ∂[u] (f1 + f2) = ∂[u] f1 + ∂[u] f2 := by
  ext x
  simp [deriv_eq, fderiv_add (hf1 x) (hf2 x)]

/-- Derivatives on space distribute coordinate-wise over addition. -/
lemma deriv_coord_add (f1 f2 : Space d → EuclideanSpace ℝ (Fin d))
    (hf1 : Differentiable ℝ f1) (hf2 : Differentiable ℝ f2) :
    (∂[u] (fun x => f1 x i + f2 x i)) =
      (∂[u] (fun x => f1 x i)) + (∂[u] (fun x => f2 x i)) :=
  deriv_add (fun x => f1 x i) (fun x => f2 x i) (by fun_prop) (by fun_prop)

/-- Derivatives on space distribute over subtraction. -/
@[to_fun]
lemma deriv_sub [NormedAddCommGroup M] [NormedSpace ℝ M]
    (f1 f2 : Space d → M) (hf1 : Differentiable ℝ f1) (hf2 : Differentiable ℝ f2) :
    ∂[u] (f1 - f2) = ∂[u] f1 - ∂[u] f2 := by
  ext x
  simp [deriv_eq, fderiv_sub (hf1 x) (hf2 x)]

/-!

### A.4. Derivative distributes over scalar multiplication

-/

/-- Space derivatives on scalar product of functions. -/
lemma deriv_smul [NormedAddCommGroup M] [NormedSpace ℝ M] [NontriviallyNormedField 𝕜]
    [NormedAlgebra ℝ 𝕜] [NormedSpace 𝕜 M] {c : Space d → 𝕜} {f : Space d → M}
    (hc : DifferentiableAt ℝ c x) (hf : DifferentiableAt ℝ f x) :
    ∂[u] (c • f) x = c x • ∂[u] f x + ∂[u] c x • f x := by
  simp [deriv_eq, fderiv_smul hc hf]

/-- Space derivatives on scalar times function. -/
lemma deriv_const_smul [NormedAddCommGroup M] [NormedSpace ℝ M] [Semiring R]
    [Module R M] [SMulCommClass ℝ R M] [ContinuousConstSMul R M] {f : Space d → M} (c : R)
    (h : Differentiable ℝ f) : ∂[u] (c • f) = c • ∂[u] f := by
  ext x
  simp [deriv_eq, fderiv_const_smul (h x) c]

/-- Coordinate-wise scalar multiplication on space derivatives. -/
lemma deriv_coord_smul (f : Space d → EuclideanSpace ℝ (Fin d)) (k : ℝ)
    (hf : Differentiable ℝ f) :
    ∂[u] (fun x => k * f x i) x = k * ∂[u] (fun x => f x i) x :=
  congrFun (deriv_const_smul (f := fun x => f x i) k (by fun_prop)) x

/-!

### A.5. Two spatial derivatives commute

-/

/-- Derivatives on space commute with one another. -/
lemma deriv_commute [NormedAddCommGroup M] [NormedSpace ℝ M]
    (f : Space d → M) (hf : ContDiff ℝ 2 f) : ∂[u] (∂[v] f) = ∂[v] (∂[u] f) := by
  simp only [deriv_eq_fderiv_fun]
  ext x
  rw [fderiv_clm_apply, fderiv_clm_apply]
  simp only [fderiv_fun_const, Pi.ofNat_apply, ContinuousLinearMap.comp_zero, zero_add,
    ContinuousLinearMap.flip_apply]
  rw [(hf.contDiffAt.isSymmSndFDerivAt (by simp)).eq]
  repeat fun_prop

/-!

### A.6. Derivative of a component

-/

@[simp]
lemma deriv_component_same (μ : Fin d) (x : Space d) :
    ∂[μ] (fun x => x μ) x = 1 := by
  simp only [← Space.coord_apply, ← Space.coordCLM_apply]
  simp only [deriv_eq, ContinuousLinearMap.fderiv]
  simp [Space.coordCLM, Space.coord]

lemma deriv_component_diff (μ ν : Fin d) (x : Space d) (h : μ ≠ ν) :
    (deriv μ (fun x => x ν) x) = 0 := by
  simp only [← Space.coord_apply, ← Space.coordCLM_apply]
  simp only [deriv_eq, ContinuousLinearMap.fderiv]
  simpa [Space.coordCLM, Space.coord, basis_apply] using h

lemma deriv_component (μ ν : Fin d) (x : Space d) :
    (deriv ν (fun x => x μ) x) = if ν = μ then 1 else 0 := by
  obtain rfl | h' := eq_or_ne ν μ
  · simp
  · simp [deriv_component_diff ν μ x h', h']

/-!

### A.7. Derivative of a component squared

-/

lemma deriv_component_sq {d : ℕ} {ν μ : Fin d} (x : Space d) :
    (deriv ν (fun x => (x μ) ^ 2) x) = if ν = μ then 2 * x μ else 0:= by
  rw [deriv_eq, fderiv_fun_pow 2 (eval_differentiable μ x)]
  simp [← deriv_eq, deriv_component, mul_ite]

/-!

### A.8. Derivative of a product of functions of single coordinates

-/

/-- The derivative in direction `μ` of `x ↦ ∏ⱼ gⱼ (xⱼ)`, a product of differentiable functions
  of one coordinate each, is `gμ' (xμ)` times the product of the other factors. -/
lemma deriv_prod_coord {d : ℕ} (g : Fin d → ℝ → ℂ) (hg : ∀ j, Differentiable ℝ (g j))
    (μ : Fin d) (x : Space d) :
    ∂[μ] (fun x : Space d => ∏ j, g j (x j)) x =
      _root_.deriv (g μ) (x μ) * ∏ j ∈ Finset.univ.erase μ, g j (x j) := by
  have hcoord : ∀ j, HasFDerivAt (fun x : Space d => x j) (coordCLM j) x := fun j => by
    convert (coordCLM j).hasFDerivAt (x := x) using 1
    funext y
    simp [coordCLM_apply, coord_apply]
  have hj : ∀ j ∈ (Finset.univ : Finset (Fin d)), HasFDerivAt (fun x : Space d => g j (x j))
      (((1 : ℝ →L[ℝ] ℝ).smulRight (_root_.deriv (g j) (x j))).comp (coordCLM j)) x :=
    fun j _ => by
      have hd : HasFDerivAt (g j) ((1 : ℝ →L[ℝ] ℝ).smulRight (_root_.deriv (g j) (x j))) (x j) :=
        (hg j).differentiableAt.hasDerivAt.hasFDerivAt
      exact hd.comp x (hcoord j)
  have h := HasFDerivAt.finsetProd hj
  rw [deriv_eq, h.fderiv]
  simp only [_root_.sum_apply, _root_.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smulRight_apply, one_apply_eq_self, smul_eq_mul]
  rw [Finset.sum_eq_single μ (fun b _ hb => by
    simp [coordCLM_apply, coord_apply, basis_apply, Ne.symm hb]) (by simp)]
  simp [coordCLM_apply, coord_apply, mul_comm]

/-!

### A.8. Derivivatives of components

-/

lemma deriv_euclid {d ν μ} {f : Space d → EuclideanSpace ℝ (Fin n)}
    (hf : Differentiable ℝ f) (x : Space d) :
    deriv ν (fun x => f x μ) x = deriv ν (fun x => f x) x μ := by
  rw [deriv_eq_fderiv_basis]
  change fderiv ℝ (EuclideanSpace.proj μ ∘ fun x => f x) x (basis ν) = _
  rw [fderiv_comp x (EuclideanSpace.proj μ).differentiableAt (hf x)]
  simp [-EuclideanSpace.coe_proj, ← deriv_eq_fderiv_basis]

lemma deriv_lorentz_vector {d ν μ} {f : Space d → Lorentz.Vector d}
    (hf : Differentiable ℝ f) (x : Space d) :
    deriv ν (fun x => f x μ) x = deriv ν (fun x => f x) x μ := by
  rw [deriv_eq_fderiv_basis]
  change fderiv ℝ (Lorentz.Vector.coordCLM μ ∘ fun x => f x) x (basis ν) = _
  rw [fderiv_comp x (Lorentz.Vector.coordCLM μ).differentiableAt (hf x)]
  simp [← deriv_eq_fderiv_basis, Lorentz.Vector.coordCLM_apply]

/-!

### A.9. Derivative of a norm squared

-/

/-!

#### A.9.1. Differentiability of the norm squared function

-/
@[fun_prop]
lemma norm_sq_differentiable : Differentiable ℝ (fun x : Space d => ‖x‖ ^ 2) :=
  (contDiff_norm_sq ℝ).differentiable one_ne_zero

/-!

#### A.9.2. Derivative of the norm squared function

-/

lemma deriv_norm_sq (x : Space d) (i : Fin d) :
    deriv i (fun x => ‖x‖ ^ 2) x = 2 * x i := by
  simp [deriv_eq, fderiv_norm_sq_apply]

/-!

### A.10. Derivative of the inner product

-/

open InnerProductSpace

/-!

#### A.10.1. Differentiability of the inner product function

-/

/-- The inner product is differentiable. -/
@[fun_prop]
lemma inner_differentiable {d : ℕ} :
    Differentiable ℝ (fun y : Space d => ⟪y, y⟫_ℝ) :=
  differentiable_id.inner ℝ differentiable_id

@[fun_prop]
lemma inner_differentiableAt {d : ℕ} (x : Space d) :
    DifferentiableAt ℝ (fun y : Space d => ⟪y, y⟫_ℝ) x :=
  inner_differentiable x

@[fun_prop]
lemma inner_apply_differentiableAt {d : ℕ} [NormedAddCommGroup M]
    [NormedSpace ℝ M]
    {f : M → Space d} {g : M → Space d} (x : M)
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    DifferentiableAt ℝ (fun y : M => ⟪f y, g y⟫_ℝ) x :=
  hf.inner ℝ hg

@[fun_prop]
lemma inner_apply_differentiable {d : ℕ} [NormedAddCommGroup M]
    [NormedSpace ℝ M]
    {f : M → Space d} {g : M → Space d}
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) :
    Differentiable ℝ (fun y : M => ⟪f y, g y⟫_ℝ) :=
  hf.inner ℝ hg
@[fun_prop]
lemma inner_contDiff {n : WithTop ℕ∞} {d : ℕ} :
    ContDiff ℝ n (fun y : Space d => ⟪y, y⟫_ℝ) :=
  contDiff_id.inner ℝ contDiff_id

@[fun_prop]
lemma inner_apply_contDiff {n : WithTop ℕ∞} {d : ℕ} [NormedAddCommGroup M]
    [NormedSpace ℝ M]
    {f : M → Space d} {g : M → Space d}
    (hf : ContDiff ℝ n f) (hg : ContDiff ℝ n g) :
    ContDiff ℝ n (fun y : M => ⟪f y, g y⟫_ℝ) :=
  hf.inner ℝ hg
/-!

#### A.10.2. Derivative of the inner product function

-/

lemma deriv_eq_inner_self (x : Space d) (i : Fin d) :
    deriv i (fun x => ⟪x, x⟫_ℝ) x = 2 * x i := by
  simpa only [real_inner_self_eq_norm_sq] using deriv_norm_sq x i

/-!

#### A.10.3. Derivative of the inner product on one side

-/

@[simp]
lemma deriv_inner_left {d} (x1 x2 : Space d) (i : Fin d) :
    deriv i (fun x => ⟪x, x2⟫_ℝ) x1 = x2 i := by
  simp [deriv_eq, fderiv_inner_apply ℝ differentiableAt_fun_id (differentiableAt_const x2)]

@[simp]
lemma deriv_inner_right {d} (x1 x2 : Space d) (i : Fin d) :
    deriv i (fun x => ⟪x1, x⟫_ℝ) x2 = x1 i := by
  simp [deriv_eq, fderiv_inner_apply ℝ (differentiableAt_const x1) differentiableAt_fun_id]
/-!

### A.11. Differentiability of derivatives

-/

lemma deriv_differentiable {M} [NormedAddCommGroup M]
    [NormedSpace ℝ M] {d : ℕ} {f : Space d → M}
    (hf : ContDiff ℝ 2 f) (i : Fin d) :
    Differentiable ℝ (deriv i f) := by
  unfold deriv
  fun_prop

open ContDiff

lemma deriv_contDiff {d} {f : Space d → ℝ} (hf : ContDiff ℝ (n + 1) f) :
    ContDiff ℝ n fun x i => deriv i f x := by
  unfold deriv
  fun_prop

/-!

## B. Derivatives of distributions on `Space d`

-/

open Distribution SchwartzMap

/-!

### B.1. The definition

-/
/-- Given a distribution (function) `f : Space d →d[ℝ] M` the derivative
  of `f` in direction `μ`. -/
noncomputable def distDeriv {M d} [NormedAddCommGroup M] [NormedSpace ℝ M]
    (μ : Fin d) : ((Space d) →d[ℝ] M) →ₗ[ℝ] (Space d) →d[ℝ] M where
  toFun f :=
    let ev : (Space d →L[ℝ] M) →L[ℝ] M := {
      toFun v := v (basis μ)
      map_add' v1 v2 := by
        simp only [_root_.add_apply]
      map_smul' a v := by
        simp
    }
    ev.comp (Distribution.fderivD ℝ f)
  map_add' f1 f2 := by
    simp
  map_smul' a f := by simp

@[inherit_doc distDeriv]
macro "∂ᵈ[" i:term "]" : term => `(distDeriv $i)

/-!

### B.2. Basic equality

-/

lemma distDeriv_apply {M d} [NormedAddCommGroup M] [NormedSpace ℝ M]
    (μ : Fin d) (f : (Space d) →d[ℝ] M) (ε : 𝓢(Space d, ℝ)) :
    (∂ᵈ[μ] f) ε = fderivD ℝ f ε (basis μ) := by
  simp [distDeriv, Distribution.fderivD]

/-!

### B.3. Commutation of derivatives

-/

lemma schwartMap_fderiv_comm {d}
    (μ ν : Fin d) (x : Space d) (η : 𝓢(Space d, ℝ)) :
    ((SchwartzMap.evalCLM ℝ (Space d) ℝ (basis μ))
      ((fderivCLM ℝ (Space d) ℝ) ((SchwartzMap.evalCLM ℝ (Space d) ℝ (basis ν))
      ((fderivCLM ℝ (Space d) ℝ) η)))) x =
    ((SchwartzMap.evalCLM ℝ (Space d) ℝ (basis ν))
      ((fderivCLM ℝ (Space d) ℝ) ((SchwartzMap.evalCLM ℝ (Space d) ℝ (basis μ))
      ((fderivCLM ℝ (Space d) ℝ) η)))) x := by
  change ∂[μ] (∂[ν] ⇑η) x = ∂[ν] (∂[μ] ⇑η) x
  exact congrFun (deriv_commute _ (η.smooth 2)) x

lemma distDeriv_commute {M d} [NormedAddCommGroup M] [NormedSpace ℝ M]
    (μ ν : Fin d) (f : (Space d) →d[ℝ] M) :
    (∂ᵈ[ν] (∂ᵈ[μ] f)) = (∂ᵈ[μ] (∂ᵈ[ν] f)) := by
  ext η
  simp [distDeriv, Distribution.fderivD]
  congr 1
  exact SchwartzMap.ext fun x => schwartMap_fderiv_comm μ ν x η

end Space
