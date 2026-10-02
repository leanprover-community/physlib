/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.SpaceAndTime.SpaceTime.LorentzAction
public import Physlib.Relativity.Tensors.RealTensor.CoVector.Tensorial
public import Mathlib.Analysis.InnerProductSpace.TensorProduct
public import Physlib.SpaceAndTime.Space.Derivatives.Basic
public import Physlib.SpaceAndTime.Time.Derivatives
/-!

# Derivatives on SpaceTime

## i. Overview

In this module we define and prove basic lemmas about derivatives of functions and
distributions on `SpaceTime d`.

## ii. Key results

- `deriv` : The derivative of a function `SpaceTime d → M` along the `μ` coordinate.
- `manifoldDeriv` : The derivative of a function from `SpaceTime d` to a manifold along
  the `μ` coordinate.
- `contDiff_deriv` : If `f` is `C^{n+1}` then `∂_ μ f` is `C^n`.
- `differentiable_deriv` : If `f` is `C^2` then `∂_ μ f` is differentiable.
- `deriv_commute` : Derivatives on `SpaceTime d` commute (Clairaut's theorem).
- `deriv_sum_inr` : The derivative along a spatial coordinate in terms of the
  derivative on `Space d`.
- `deriv_sum_inl` : The derivative along the temporal coordinate in terms of the
  derivative on `Time`.
- `iteratedDeriv` : Iterated derivatives along a multiset of coordinates.
- `distDeriv` : The derivative of a distribution on `SpaceTime d` along the `μ` coordinate.
- `distDeriv_commute` : Derivatives of distributions on `SpaceTime d` commute.

## iii. Table of contents

- A. Derivatives of functions on `SpaceTime d`
  - A.1. The definition of the derivative
  - A.2. Basic equality lemmas
  - A.3. Linearity of the derivative
  - A.4. Smoothness and differentiability of the derivative
  - A.5. Derivatives commute
  - A.6. The derivative of a function composed with a Lorentz transformation
  - A.7. Spacetime derivatives in terms of time and space derivatives
  - A.8. Iterated derivatives
- B. Derivatives of distributions
  - B.1. Commutation of derivatives of distributions
  - B.2. Lorentz group action on derivatives of distributions
- C. Derivatives of tensors
  - C.1. Derivatives of tensors for distributions

## iv. References

* None.
-/

@[expose] public section
noncomputable section

namespace SpaceTime

open Manifold
open Matrix
open Complex
open ComplexConjugate
open TensorSpecies
open Physlib
/-!

## A. Derivatives of functions on `SpaceTime d`

-/

/-!

### A.1. The definition of the derivative

-/

/-- The derivative of a function `SpaceTime d → ℝ` along the `μ` coordinate. -/
noncomputable def deriv {M : Type} [AddCommGroup M] [Module ℝ M] [TopologicalSpace M]
    {d : ℕ} (μ : Fin 1 ⊕ Fin d) (f : SpaceTime d → M) : SpaceTime d → M :=
  fun y => fderiv ℝ f y (Lorentz.Vector.basis μ)

@[inherit_doc deriv]
scoped notation "∂_" => deriv

lemma deriv_eq {M : Type} [AddCommGroup M] [Module ℝ M] [TopologicalSpace M]
    {d : ℕ} (μ : Fin 1 ⊕ Fin d) (f : SpaceTime d → M) (y : SpaceTime d) :
    ∂_ μ f y =
    fderiv ℝ f y (Lorentz.Vector.basis μ) := by
  rfl

/-- The derivative of a function from `SpaceTime d` to a manifold along the `μ`
coordinate, as a tangent vector at the value of the function. -/
noncomputable def manifoldDeriv {E H N : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [TopologicalSpace N]
    [ChartedSpace H N] {d : ℕ} (μ : Fin 1 ⊕ Fin d) (f : SpaceTime d → N) :
    (y : SpaceTime d) → TangentSpace I (f y) :=
  fun y => mfderiv 𝓘(ℝ, SpaceTime d) I f y
    ((Lorentz.Vector.basis μ : SpaceTime d) : TangentSpace 𝓘(ℝ, SpaceTime d) y)

lemma manifoldDeriv_eq {E H N : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [TopologicalSpace N]
    [ChartedSpace H N] {d : ℕ} (μ : Fin 1 ⊕ Fin d) (f : SpaceTime d → N)
    (y : SpaceTime d) :
    manifoldDeriv I μ f y =
      mfderiv 𝓘(ℝ, SpaceTime d) I f y
        ((Lorentz.Vector.basis μ : SpaceTime d) : TangentSpace 𝓘(ℝ, SpaceTime d) y) := rfl

/-- The spacetime derivative is the manifold derivative for functions into normed spaces. -/
lemma deriv_eq_mfderiv {M : Type} [NormedAddCommGroup M] [NormedSpace ℝ M]
    {d : ℕ} (μ : Fin 1 ⊕ Fin d) (f : SpaceTime d → M) (y : SpaceTime d) :
    deriv μ f y =
      mfderiv 𝓘(ℝ, SpaceTime d) 𝓘(ℝ, M) f y
        ((Lorentz.Vector.basis μ : SpaceTime d) : TangentSpace 𝓘(ℝ, SpaceTime d) y) := by
  rw [deriv_eq, ← mfderiv_eq_fderiv]
  rfl

lemma deriv_eq_manifoldDeriv {M : Type} [NormedAddCommGroup M] [NormedSpace ℝ M]
    {d : ℕ} (μ : Fin 1 ⊕ Fin d) (f : SpaceTime d → M) (y : SpaceTime d) :
    deriv μ f y = manifoldDeriv 𝓘(ℝ, M) μ f y := by
  rw [deriv_eq_mfderiv, manifoldDeriv_eq]

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma manifoldDeriv_const {E H N : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [TopologicalSpace N]
    [ChartedSpace H N] {d : ℕ} (μ : Fin 1 ⊕ Fin d) (n : N) (y : SpaceTime d) :
    manifoldDeriv I μ (fun _ : SpaceTime d => n) y = 0 := by
  simp [manifoldDeriv]

/-!

### A.2. Basic equality lemmas

-/

variable {M : Type} [AddCommGroup M] [Module ℝ M] [TopologicalSpace M]

lemma differentiable_vector {d : ℕ} (f : SpaceTime d → Lorentz.Vector d) :
    (∀ ν, Differentiable ℝ (fun x => f x ν)) ↔ Differentiable ℝ f := by
  refine ⟨fun h => ?_, fun h ν => ?_⟩
  · rw [← (Lorentz.Vector.equivPi d).comp_differentiable_iff]
    exact differentiable_pi'' h
  · exact (Lorentz.Vector.coordCLM ν).differentiable.comp h

lemma contDiff_vector {d : ℕ} (f : SpaceTime d → Lorentz.Vector d) :
    (∀ ν, ContDiff ℝ n (fun x => f x ν)) ↔ ContDiff ℝ n f := by
  refine ⟨fun h => ?_, fun h ν => ?_⟩
  · rw [← (Lorentz.Vector.equivPi d).comp_contDiff_iff]
    exact contDiff_pi' h
  · exact (Lorentz.Vector.coordCLM ν).contDiff.comp h

lemma fderiv_vector {d : ℕ} (f : SpaceTime d → Lorentz.Vector d)
    (hf : Differentiable ℝ f) (y dt : SpaceTime d) (ν : Fin 1 ⊕ Fin d) :
    fderiv ℝ f y dt ν = fderiv ℝ (fun x => f x ν) y dt := by
  change _ = (fderiv ℝ (Lorentz.Vector.coordCLM ν ∘ f) y) dt
  rw [fderiv_comp _ (by fun_prop) (by fun_prop)]
  simp only [ContinuousLinearMap.fderiv, ContinuousLinearMap.coe_comp, Function.comp_apply,
    Lorentz.Vector.coordCLM_apply]

lemma deriv_apply_eq {d : ℕ} (μ ν : Fin 1 ⊕ Fin d) (f : SpaceTime d → Lorentz.Vector d)
    (hf : Differentiable ℝ f)
    (y : SpaceTime d) :
    ∂_ μ f y ν = fderiv ℝ (fun x => f x ν) y (Lorentz.Vector.basis μ) :=
  fderiv_vector f hf y _ ν

@[simp]
lemma deriv_coord {d : ℕ} (μ ν : Fin 1 ⊕ Fin d) :
    ∂_ μ (fun x => x ν) = if μ = ν then 1 else 0 := by
  change ∂_ μ (coordCLM ν) = _
  funext x
  rw [deriv_eq]
  simp only [ContinuousLinearMap.fderiv]
  simp [coordCLM]
  split_ifs <;> rfl

/-!

### A.3. Linearity of the derivative

-/

@[simp]
lemma deriv_zero {d : ℕ} (μ : Fin 1 ⊕ Fin d) : SpaceTime.deriv μ (fun _ => (0 : ℝ)) = 0 := by
  ext y
  simp [SpaceTime.deriv_eq]

/-- Derivatives on spacetime distribute over addition. -/
@[to_fun]
lemma deriv_add {M : Type} [NormedAddCommGroup M] [NormedSpace ℝ M] {d : ℕ}
    (μ : Fin 1 ⊕ Fin d) (f g : SpaceTime d → M) (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) :
    ∂_ μ (f + g) = ∂_ μ f + ∂_ μ g := by
  ext x
  simp [deriv_eq, fderiv_add (hf x) (hg x)]

/-- Derivatives on spacetime commute with multiplication by a constant. -/
lemma deriv_const_smul {M R : Type} [NormedAddCommGroup M] [NormedSpace ℝ M] [Semiring R]
    [Module R M] [SMulCommClass ℝ R M] [ContinuousConstSMul R M] {d : ℕ}
    (μ : Fin 1 ⊕ Fin d) (c : R) {f : SpaceTime d → M} (hf : Differentiable ℝ f) :
    ∂_ μ (c • f) = c • ∂_ μ f := by
  ext x
  simp [deriv_eq, fderiv_const_smul (hf x) c]

attribute [-simp] Fintype.sum_sum_type

/-!

### A.4. Smoothness and differentiability of the derivative

-/

/-- If `f` is `C^{n+1}` then `∂_ μ f` is `C^n`. -/
@[fun_prop]
lemma contDiff_deriv {M : Type} [NormedAddCommGroup M] [NormedSpace ℝ M] {d : ℕ}
    {n : WithTop ℕ∞} (μ : Fin 1 ⊕ Fin d) (f : SpaceTime d → M) (hf : ContDiff ℝ (n + 1) f) :
    ContDiff ℝ n (∂_ μ f) := by
  -- `∂_ μ f = fun x => fderiv ℝ f x (Lorentz.Vector.basis μ)`; use
  -- `ContDiff.clm_apply` with `ContDiff.fderiv_right`.
  exact (ContDiff.fderiv_right (m := n) hf (by rfl)).clm_apply contDiff_const

/-- If `f` is `C^2` then `∂_ μ f` is differentiable. -/
@[fun_prop]
lemma differentiable_deriv {M : Type} [NormedAddCommGroup M] [NormedSpace ℝ M] {d : ℕ}
    (μ : Fin 1 ⊕ Fin d) (f : SpaceTime d → M) (hf : ContDiff ℝ 2 f) :
    Differentiable ℝ (∂_ μ f) :=
  (contDiff_deriv μ f (n := 1) (by norm_cast)).differentiable one_ne_zero

/-!

### A.5. Derivatives commute

-/

/-- Derivatives on spacetime commute with one another (Clairaut's theorem). -/
lemma deriv_commute {M : Type} [NormedAddCommGroup M] [NormedSpace ℝ M] {d : ℕ}
    (μ ν : Fin 1 ⊕ Fin d) (f : SpaceTime d → M) (hf : ContDiff ℝ 2 f) :
    ∂_ μ (∂_ ν f) = ∂_ ν (∂_ μ f) := by
  ext x
  show fderiv ℝ (fun y => fderiv ℝ f y (Lorentz.Vector.basis ν)) x (Lorentz.Vector.basis μ) =
    fderiv ℝ (fun y => fderiv ℝ f y (Lorentz.Vector.basis μ)) x (Lorentz.Vector.basis ν)
  rw [fderiv_clm_apply, fderiv_clm_apply]
  simp only [fderiv_fun_const, Pi.ofNat_apply, ContinuousLinearMap.comp_zero, zero_add,
    ContinuousLinearMap.flip_apply]
  rw [IsSymmSndFDerivAt.eq]
  · exact hf.contDiffAt.isSymmSndFDerivAt (by simp [minSmoothness_of_isRCLikeNormedField])
  all_goals fun_prop

open scoped ContDiff

/-- For a smooth function, iterated derivatives along a list of directions do not depend on the
  order of the list. -/
lemma foldl_deriv_perm {M : Type} [NormedAddCommGroup M] [NormedSpace ℝ M] {d : ℕ}
    {l₁ l₂ : List (Fin 1 ⊕ Fin d)} (h : l₁.Perm l₂) {f : SpaceTime d → M}
    (hf : ContDiff ℝ ∞ f) :
    l₁.foldl (fun g μ => ∂_ μ g) f = l₂.foldl (fun g μ => ∂_ μ g) f := by
  induction h generalizing f with
  | nil => rfl
  | cons μ _ ih => exact ih (contDiff_deriv μ f (by simpa using hf))
  | swap μ ν l =>
    simp only [List.foldl_cons]
    rw [deriv_commute _ _ f (hf.of_le (by simp))]
  | trans _ _ ih₁ ih₂ => exact (ih₁ hf).trans (ih₂ hf)

/-!

### A.6. The derivative of a function composed with a Lorentz transformation

-/

lemma deriv_comp_lorentz_action {M : Type} [NormedAddCommGroup M] [NormedSpace ℝ M] {d : ℕ}
    (μ : Fin 1 ⊕ Fin d)
    (f : SpaceTime d → M) (hf : Differentiable ℝ f) (Λ : LorentzGroup d)
    (x : SpaceTime d) :
    ∂_ μ (fun x => f (Λ • x)) x = ∑ ν, Λ.1 ν μ • ∂_ ν f (Λ • x) := by
  change fderiv ℝ (f ∘ Lorentz.Vector.actionCLM Λ) x (Lorentz.Vector.basis μ) = _
  rw [fderiv_comp]
  simp only [Lorentz.Vector.actionCLM_apply, ContinuousLinearMap.fderiv,
    ContinuousLinearMap.coe_comp, Function.comp_apply]
    -- Fintype.sum_sum_type
  rw [Lorentz.Vector.smul_basis]
  simp [deriv_eq]
  · fun_prop
  · fun_prop

variable
    {c : Fin n → realLorentzTensor.Color} {M : Type} [NormedAddCommGroup M]
      [NormedSpace ℝ M] [Tensorial (realLorentzTensor d) c M] [T2Space M]
lemma deriv_equivariant (f : SpaceTime d → M) (Λ : LorentzGroup d) (x : SpaceTime d)
    (hf : Differentiable ℝ f) (μ : Fin 1 ⊕ Fin d) :
    ∂_ μ (fun x => Λ • f (Λ⁻¹ • x)) x =
    ∑ ν, Λ⁻¹.1 ν μ • Λ • ∂_ ν f (Λ⁻¹ • x) := by
  have h1 (μ : Fin 1 ⊕ Fin d) (x : SpaceTime d) :
      ∂_ μ (fun x => Λ • f (Λ⁻¹ • x)) x =
      Λ • ∂_ μ (fun x => f (Λ⁻¹ • x)) x := by
    change ∂_ μ (TensorSpecies.Tensorial.actionCLM _ Λ ∘ fun x => f (Λ⁻¹ • x)) x = _
    rw [deriv_eq, fderiv_comp]
    simp [Tensorial.actionCLM_apply, ← deriv_eq]
    · fun_prop
    · exact (hf.comp (Lorentz.Vector.actionCLM Λ⁻¹).differentiable).differentiableAt
  rw [h1 μ x, deriv_comp_lorentz_action]
  change (TensorSpecies.Tensorial.actionCLM _ Λ) (∑ ν, (Λ⁻¹).1 ν μ • ∂_ ν f (Λ⁻¹ • x)) = _
  simp [TensorSpecies.Tensorial.actionCLM_apply, map_sum, map_smul]
  · fun_prop

/-!

### A.7. Spacetime derivatives in terms of time and space derivatives

-/

lemma deriv_sum_inr {d : ℕ} {M : Type} [NormedAddCommGroup M] [NormedSpace ℝ M]
    (c : SpeedOfLight) (f : SpaceTime d → M)
    (hf : Differentiable ℝ f) (x : SpaceTime d) (i : Fin d) :
    ∂_ (Sum.inr i) f x
    = Space.deriv i (fun y => f ((toTimeAndSpace c).symm ((toTimeAndSpace c x).1, y)))
      (toTimeAndSpace c x).2 := by
  rw [deriv_eq, Space.deriv_eq]
  conv_rhs => rw [fderiv_fun_comp _ (by fun_prop) (by fun_prop)]
  simp only [Prod.mk.eta, ContinuousLinearEquiv.symm_apply_apply, ContinuousLinearMap.coe_comp,
    Function.comp_apply]
  congr 1
  rw [fderiv_fun_comp]
  simp only [Prod.mk.eta, toTimeAndSpace_symm_fderiv, ContinuousLinearMap.coe_comp,
    ContinuousLinearEquiv.coe_coe, Function.comp_apply]
  change _ = (toTimeAndSpace c).symm ((fderiv ℝ ((toTimeAndSpace c x).1, ·) (toTimeAndSpace c x).2)
    (Space.basis i))
  rw [DifferentiableAt.fderiv_prodMk]
  simp only [fderiv_fun_const, Pi.zero_apply, fderiv_fun_id, ContinuousLinearMap.prod_apply,
    _root_.zero_apply, ContinuousLinearMap.coe_id', id_eq]
  trans (toTimeAndSpace c).symm (0, Space.basis i)
  · rw [← toTimeAndSpace_basis_inr (c := c)]
    simp
  · rfl
  repeat' fun_prop

lemma deriv_sum_inl {d : ℕ} {M : Type} [NormedAddCommGroup M]
    [NormedSpace ℝ M] (c : SpeedOfLight) (f : SpaceTime d → M)
    (hf : Differentiable ℝ f) (x : SpaceTime d) :
    ∂_ (Sum.inl 0) f x
    = (1/(c : ℝ)) • Time.deriv (fun t => f ((toTimeAndSpace c).symm (t, (toTimeAndSpace c x).2)))
      (toTimeAndSpace c x).1 := by
  rw [deriv_eq, Time.deriv_eq]
  conv_rhs => rw [fderiv_fun_comp _ (by fun_prop) (by fun_prop)]
  simp only [Fin.isValue, Prod.mk.eta, ContinuousLinearEquiv.symm_apply_apply,
    ContinuousLinearMap.coe_comp, Function.comp_apply]
  trans
    (fderiv ℝ f x)
      ((1 / c.val) • (fderiv ℝ (fun t => (toTimeAndSpace c).symm (t, ((toTimeAndSpace c) x).2))
      ((toTimeAndSpace c) x).1) 1)
  swap
  · exact ContinuousLinearMap.map_smul_of_tower (fderiv ℝ f x) (1 / c.val) _
  congr 1

  rw [fderiv_fun_comp]
  simp only [Fin.isValue, Prod.mk.eta, toTimeAndSpace_symm_fderiv, ContinuousLinearMap.coe_comp,
    ContinuousLinearEquiv.coe_coe, Function.comp_apply]
  rw [DifferentiableAt.fderiv_prodMk]
  simp only [Fin.isValue, fderiv_fun_id, fderiv_fun_const, Pi.zero_apply,
    ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_id', id_eq,
    _root_.zero_apply]
  rw [← map_smul]
  rw [← toTimeAndSpace_basis_inl' (c := c)]
  simp only [Fin.isValue, ContinuousLinearEquiv.symm_apply_apply]
  repeat' fun_prop

/-!

### A.8. Iterated derivatives

Derivatives along different directions commute for smooth functions, so an iterated derivative of
a smooth function depends only on how many times each direction occurs. We therefore index iterated
derivatives by a multiset `s` of directions and write `iteratedDeriv s f`. For an arbitrary function
the derivatives are taken in the order of the list `s.toList`, and the lemmas that reorder
directions assume that `f` is smooth.

-/

/-- The iterated derivative of `f`, differentiating once along each element of `s`. -/
noncomputable def iteratedDeriv {M : Type} [AddCommGroup M] [Module ℝ M] [TopologicalSpace M]
    {d : ℕ} (s : Multiset (Fin 1 ⊕ Fin d)) (f : SpaceTime d → M) : SpaceTime d → M :=
  s.toList.foldl (fun g μ => ∂_ μ g) f

@[simp]
lemma iteratedDeriv_zero {M : Type} [AddCommGroup M] [Module ℝ M] [TopologicalSpace M] {d : ℕ}
    (f : SpaceTime d → M) :
    iteratedDeriv 0 f = f := by
  simp [iteratedDeriv]

@[simp]
lemma iteratedDeriv_singleton {M : Type} [AddCommGroup M] [Module ℝ M] [TopologicalSpace M]
    {d : ℕ} (μ : Fin 1 ⊕ Fin d) (f : SpaceTime d → M) :
    iteratedDeriv {μ} f = ∂_ μ f := by
  simp [iteratedDeriv]

/-- Iterated derivatives of a smooth function are smooth. -/
lemma contDiff_iteratedDeriv {M : Type} [NormedAddCommGroup M] [NormedSpace ℝ M] {d : ℕ}
    (s : Multiset (Fin 1 ⊕ Fin d)) {f : SpaceTime d → M} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (iteratedDeriv s f) := by
  unfold iteratedDeriv
  induction s.toList generalizing f with
  | nil => exact hf
  | cons μ l ih => exact ih (contDiff_deriv μ f (by simpa using hf))

/-- An iterated derivative of a smooth function may begin with any of its directions. -/
lemma iteratedDeriv_cons {M : Type} [NormedAddCommGroup M] [NormedSpace ℝ M] {d : ℕ}
    (μ : Fin 1 ⊕ Fin d) (s : Multiset (Fin 1 ⊕ Fin d)) {f : SpaceTime d → M}
    (hf : ContDiff ℝ ∞ f) :
    iteratedDeriv (μ ::ₘ s) f = iteratedDeriv s (∂_ μ f) := by
  have hp : (μ ::ₘ s).toList.Perm (μ :: s.toList) :=
    Multiset.coe_eq_coe.mp (by rw [Multiset.coe_toList, ← Multiset.cons_coe, Multiset.coe_toList])
  exact foldl_deriv_perm hp hf

/-- Iterated derivatives of smooth functions distribute over addition. -/
lemma iteratedDeriv_add {M : Type} [NormedAddCommGroup M] [NormedSpace ℝ M] {d : ℕ}
    (s : Multiset (Fin 1 ⊕ Fin d)) {f g : SpaceTime d → M} (hf : ContDiff ℝ ∞ f)
    (hg : ContDiff ℝ ∞ g) :
    iteratedDeriv s (f + g) = iteratedDeriv s f + iteratedDeriv s g := by
  unfold iteratedDeriv
  induction s.toList generalizing f g with
  | nil => rfl
  | cons μ l ih =>
    simp only [List.foldl_cons]
    rw [deriv_add μ f g (hf.differentiable (by simp)) (hg.differentiable (by simp))]
    exact ih (contDiff_deriv μ f (by simpa using hf)) (contDiff_deriv μ g (by simpa using hg))

/-- Iterated derivatives of smooth functions commute with multiplication by a constant. -/
lemma iteratedDeriv_const_smul {M R : Type} [NormedAddCommGroup M] [NormedSpace ℝ M] [Semiring R]
    [Module R M] [SMulCommClass ℝ R M] [ContinuousConstSMul R M] {d : ℕ}
    (s : Multiset (Fin 1 ⊕ Fin d)) (c : R) {f : SpaceTime d → M} (hf : ContDiff ℝ ∞ f) :
    iteratedDeriv s (c • f) = c • iteratedDeriv s f := by
  unfold iteratedDeriv
  induction s.toList generalizing f with
  | nil => rfl
  | cons μ l ih =>
    simp only [List.foldl_cons]
    rw [deriv_const_smul μ c (hf.differentiable (by simp))]
    exact ih (contDiff_deriv μ f (by simpa using hf))

/-!

## B. Derivatives of distributions

-/

open Distribution SchwartzMap

/-- Given a distribution (function) `f : SpaceTime d →d[ℝ] M` the derivative
  of `f` in direction `μ`. -/
noncomputable def distDeriv {M d} [NormedAddCommGroup M] [NormedSpace ℝ M]
    (μ : Fin 1 ⊕ Fin d) : ((SpaceTime d) →d[ℝ] M) →ₗ[ℝ] (SpaceTime d) →d[ℝ] M where
  toFun f :=
    let ev : (SpaceTime d →L[ℝ] M) →L[ℝ] M := {
      toFun v := v (Lorentz.Vector.basis μ)
      map_add' v1 v2 := by
        simp only [_root_.add_apply]
      map_smul' a v := by
        simp
    }
    ev.comp (Distribution.fderivD ℝ f)
  map_add' f1 f2 := by
    simp
  map_smul' a f := by simp

lemma distDeriv_apply {M d} [NormedAddCommGroup M] [NormedSpace ℝ M]
    (μ : Fin 1 ⊕ Fin d) (f : (SpaceTime d) →d[ℝ] M) (ε : 𝓢(SpaceTime d, ℝ)) :
    distDeriv μ f ε = fderivD ℝ f ε (Lorentz.Vector.basis μ) := by
  simp [distDeriv, Distribution.fderivD]

lemma distDeriv_apply' {M d} [NormedAddCommGroup M] [NormedSpace ℝ M]
    (μ : Fin 1 ⊕ Fin d) (f : (SpaceTime d) →d[ℝ] M) (ε : 𝓢(SpaceTime d, ℝ)) :
    distDeriv μ f ε =
    - f ((SchwartzMap.evalCLM ℝ (SpaceTime d) ℝ (Lorentz.Vector.basis μ))
    ((fderivCLM ℝ (SpaceTime d) ℝ) ε)) := by
  simp [distDeriv_apply, Distribution.fderivD]

lemma apply_fderiv_eq_distDeriv {M d} [NormedAddCommGroup M] [NormedSpace ℝ M]
    (μ : Fin 1 ⊕ Fin d) (f : (SpaceTime d) →d[ℝ] M) (ε : 𝓢(SpaceTime d, ℝ)) :
    f ((SchwartzMap.evalCLM ℝ (SpaceTime d) ℝ (Lorentz.Vector.basis μ))
    ((fderivCLM ℝ (SpaceTime d) ℝ) ε)) =
    - distDeriv μ f ε := by
  simp [distDeriv_apply']

/-!

### B.1. Commutation of derivatives of distributions

-/

open ContDiff
lemma distDeriv_commute {M d} [NormedAddCommGroup M] [NormedSpace ℝ M]
    (μ ν : Fin 1 ⊕ Fin d) (f : (SpaceTime d) →d[ℝ] M) :
    distDeriv μ (distDeriv ν f) = distDeriv ν (distDeriv μ f) := by
  ext κ
  simp only [distDeriv_apply, fderivD_apply, neg_neg]
  congr 1
  ext x
  exact congrFun (deriv_commute ν μ ⇑κ (smooth κ 2)) x

/-!

### B.2. Lorentz group action on derivatives of distributions

We now show how the Lorentz group action on distributions interacts with derivatives.

-/

lemma distDeriv_comp_lorentz_action {μ : Fin 1 ⊕ Fin d} (Λ : LorentzGroup d)
    (f : (SpaceTime d) →d[ℝ] M) :
    distDeriv μ (Λ • f) = ∑ ν, Λ⁻¹.1 ν μ • (Λ • distDeriv ν f) := by
  symm
  trans (∑ ν, Λ • Λ⁻¹.1 ν μ • (distDeriv ν) f)
  · congr
    funext i
    rw [SMulCommClass.smul_comm]
  trans Λ • (∑ ν, Λ⁻¹.1 ν μ • (distDeriv ν) f)
  · exact Eq.symm Finset.smul_sum
  ext η
  rw [lorentzGroup_smul_dist_apply, distDeriv_apply, fderivD_apply,
    lorentzGroup_smul_dist_apply]
  rw [← smul_neg]
  congr
  rw [_root_.sum_apply]
  simp only [FunLike.coe_smul, Pi.smul_apply]
  conv_lhs =>
    enter [2, x]
    rw [distDeriv_apply, fderivD_apply]
    simp only [smul_neg]
    rw [← map_smul]
  rw [Finset.sum_neg_distrib]
  congr
  rw [← map_sum]
  congr
  /- Reduced to Schwartz maps -/
  ext x
  rw [_root_.sum_apply]
  symm
  simp [schwartzAction_apply]
  change ∂_ μ η (Λ • x) = ∑ ν, Λ⁻¹.1 ν μ • ∂_ ν (schwartzAction Λ⁻¹ η) (x)
  obtain ⟨η, rfl⟩ := schwartzAction_surjective Λ η
  simp only [smul_eq_mul]
  rw [schwartzAction_mul_apply]
  simp only [inv_mul_cancel, map_one, one_apply_eq_self]
  change ∂_ μ (fun x => η (Λ⁻¹ • x)) (Λ • x) = _
  rw [deriv_comp_lorentz_action]
  simp only [inv_smul_smul, smul_eq_mul]
  exact SchwartzMap.differentiable η

/-!

## C. Derivatives of tensors

Given a function `f : SpaceTime d → M` where `M` is a tensor space, we can define the
derivative of `f` as a tensor. In particular this is `∂_μ f` viewed as a tensor in
`Lorentz.CoVector d ⊗[ℝ] M`.

-/
open TensorProduct

/-- The derivative of a tensor, as a tensor. -/
def tensorDeriv (f : SpaceTime d → M) :
    SpaceTime d → Lorentz.CoVector d ⊗[ℝ] M := fun x =>
  ∑ μ, (Lorentz.CoVector.basis μ) ⊗ₜ (∂_ μ f x)

lemma tensorDeriv_equivariant (f : SpaceTime d → M) (Λ : LorentzGroup d) (x : SpaceTime d)
    (hf : Differentiable ℝ f) :
    tensorDeriv (fun x => Λ • f (Λ⁻¹ • x)) x =
    Λ • tensorDeriv f (Λ⁻¹ • x) := by
  simp [tensorDeriv]
  conv_lhs =>
    enter [2, μ]
    rw [deriv_equivariant f Λ x hf μ, tmul_sum]
    enter [2, ν]
    rw [← smul_tmul]
  rw [Finset.sum_comm]
  conv_lhs =>
    enter [2, ν]
    rw [← sum_tmul, ← Lorentz.CoVector.smul_basis, ← Tensorial.smul_prod]
  change _ = (TensorSpecies.Tensorial.smulLinearMap Λ) _
  simp [TensorSpecies.Tensorial.smulLinearMap_apply, map_sum]

open TensorSpecies.Tensorial Lorentz Tensor

lemma tensorDeriv_toTensor_basis_repr
    {f : SpaceTime d → M}
    (hf : Differentiable ℝ f) (x : SpaceTime d)
    (b : Tensor.ComponentIdx (Fin.append ![realLorentzTensor.Color.down] c)) :
    (Tensor.basis _).repr (Tensorial.toTensor (tensorDeriv f x)) b =
    ∂_ (Lorentz.CoVector.indexEquiv (ComponentIdx.prod b).1)
      (fun x => (Tensor.basis _).repr (Tensorial.toTensor (f x))
        (ComponentIdx.prod b).2) x := by
  simp [tensorDeriv]
  conv_lhs =>
    enter [2, μ]
    rw [Tensorial.toTensor_tprod, Tensor.prodT_basis_repr_apply]
    simp [Lorentz.CoVector.toTensor_basis_eq_tensor_basis, Finsupp.single_apply]
  rw [Finset.sum_eq_single (Lorentz.CoVector.indexEquiv (ComponentIdx.prod b).1)]
  · simp
    generalize (Lorentz.CoVector.indexEquiv (ComponentIdx.prod b).1) = μ at *
    generalize (ComponentIdx.prod b).2 = ν at *
    have h1 (x : SpaceTime d) : ((Tensor.basis c).repr (Tensorial.toTensor (f x))) ν =
        (ContinuousLinearMap.proj ν ∘L ((Tensor.basis c).map
        (Tensorial.toTensor).symm).equivFunL.toContinuousLinearMap) (f x) := by
      simp
    conv_rhs =>
      enter [2, x]
      rw [h1 x]
    conv_rhs =>
      rw [deriv_eq, fderiv_fun_comp _ (by fun_prop) (by fun_prop)]
    rw [ContinuousLinearMap.fderiv]
    simp [deriv_eq]
  · intro b' _ hb
    simp only [ite_eq_right_iff]
    intro hx
    exact absurd (CoVector.indexEquiv.symm_apply_eq.mp hx) hb
  · simp

/-- The expansion of `tensorDeriv` in terms of the tensor basis vector. -/
lemma tensorDeriv_eq_sum_tensor_basis
    {f : SpaceTime d → M} (hf : Differentiable ℝ f) (x : SpaceTime d) :
    tensorDeriv f x = ∑ b, ∂_ (CoVector.indexEquiv (ComponentIdx.prod b).1)
      (fun x => (Tensor.basis _).repr (toTensor (f x)) (ComponentIdx.prod b).2) x •
    toTensor.symm (Tensor.basis _ b) := by
  apply Tensorial.toTensor.injective
  apply (Tensor.basis (Fin.append _ _)).repr.injective
  ext b
  simp [Finsupp.single_apply, tensorDeriv_toTensor_basis_repr hf]

/-!

### C.1. Derivatives of tensors for distributions

-/
open InnerProductSpace
/-- The derivative of a tensor, as a tensor for distributions. -/
def distTensorDeriv {M d} [NormedAddCommGroup M]
    [InnerProductSpace ℝ M] [FiniteDimensional ℝ M] :
    ((SpaceTime d) →d[ℝ] M) →ₗ[ℝ] ((SpaceTime d) →d[ℝ] Lorentz.CoVector d ⊗[ℝ] M) where
  toFun f := {
    toFun ε := ∑ μ, (Lorentz.CoVector.basis μ) ⊗ₜ distDeriv μ f ε
    map_add' ε1 ε2 := by
      simp [← Finset.sum_add_distrib, tmul_add]
    map_smul' a ε := by
      simp [← Finset.smul_sum, tmul_smul]
    cont := by
      refine continuous_finsetSum Finset.univ (fun μ _ => ?_)
      refine Continuous.comp' ?_ ?_
      · change Continuous (fun y => (Lorentz.CoVector.basis μ) ⊗ₜ y)
        obtain ⟨w,b,hb1⟩ := exists_orthonormalBasis ℝ M
        have h1 : ∀ (y : M), (Lorentz.CoVector.basis μ) ⊗ₜ y =
            ∑ i, ⟪b i, y⟫_ℝ • ((Lorentz.CoVector.basis μ) ⊗ₜ[ℝ] (b i)) := by
          intro y
          conv_lhs => rw [← OrthonormalBasis.sum_repr' b y]
          simp [tmul_sum]
        conv => enter [1, y]; rw [h1]
        fun_prop
      · fun_prop
  }
  map_add' f1 f2 := by
    ext ε
    simp [tmul_add, Finset.sum_add_distrib]
  map_smul' a f := by
    ext ε
    simp [tmul_smul, Finset.smul_sum]

lemma distTensorDeriv_apply {M d} [NormedAddCommGroup M]
    [InnerProductSpace ℝ M] [FiniteDimensional ℝ M] (f : (SpaceTime d) →d[ℝ] M)
    (ε : 𝓢(SpaceTime d, ℝ)) :
    distTensorDeriv f ε = ∑ μ, (Lorentz.CoVector.basis μ) ⊗ₜ distDeriv μ f ε := by
  simp [distTensorDeriv]

lemma distTensorDeriv_equivariant {M : Type} [NormedAddCommGroup M]
    [InnerProductSpace ℝ M] [FiniteDimensional ℝ M] [(realLorentzTensor d).Tensorial c M]
    (f : (SpaceTime d) →d[ℝ] M) (Λ : LorentzGroup d) :
    distTensorDeriv (Λ • f) = Λ • distTensorDeriv f := by
  ext ε
  rw [distTensorDeriv_apply]
  conv_lhs =>
    enter [2, μ]
    rw [distDeriv_comp_lorentz_action]
    simp only [FunLike.coe_sum, FunLike.coe_smul, Finset.sum_apply,
      Pi.smul_apply]
    rw [tmul_sum]
    enter [2, ν]
    rw [← smul_tmul, lorentzGroup_smul_dist_apply]
  rw [Finset.sum_comm]
  conv_lhs =>
    enter [2, ν]
    rw [← sum_tmul, ← Lorentz.CoVector.smul_basis, ← Tensorial.smul_prod]
  change _ = (TensorSpecies.Tensorial.smulLinearMap Λ) _
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, ContinuousLinearMap.coe_comp,
    ContinuousLinearMap.coe_coe, Function.comp_apply]
  rw [distTensorDeriv_apply]
  simp [TensorSpecies.Tensorial.smulLinearMap_apply, map_sum]

lemma distTensorDeriv_toTensor_basis_repr {M : Type} [NormedAddCommGroup M]
    [InnerProductSpace ℝ M] [FiniteDimensional ℝ M] [(realLorentzTensor d).Tensorial c M]
    {f : (SpaceTime d) →d[ℝ] M}
    (ε : 𝓢(SpaceTime d, ℝ))
    (b : Tensor.ComponentIdx (Fin.append ![realLorentzTensor.Color.down] c)) :
    (Tensor.basis _).repr (Tensorial.toTensor (distTensorDeriv f ε)) b =
    (Tensor.basis _).repr (Tensorial.toTensor
    (distDeriv (Lorentz.CoVector.indexEquiv (ComponentIdx.prod b).1) f ε))
    (ComponentIdx.prod b).2 := by
  simp [distTensorDeriv]
  conv_lhs =>
    enter [2, μ]
    rw [Tensorial.toTensor_tprod, Tensor.prodT_basis_repr_apply]
    simp [Lorentz.CoVector.toTensor_basis_eq_tensor_basis, Finsupp.single_apply]
  rw [Finset.sum_eq_single (Lorentz.CoVector.indexEquiv (ComponentIdx.prod b).1)]
  · simp
  · intro b' _ hb
    simp only [ite_eq_right_iff]
    intro hx
    exact absurd (CoVector.indexEquiv.symm_apply_eq.mp hx) hb
  · simp

end SpaceTime

end
