/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhi Kai Pong, Joseph Tooby-Smith
-/
module

public import PhysLean.SpaceAndTime.Space.Derivatives.Curl
/-!

# Functions and distributions on Time and Space d

## i. Overview

In this module we define and prove basic lemmas about derivatives of functions and
distributions on both `Time` and `Space d`.

We put these results in the namespace `Space` by convention.

## ii. Key results

- `distTimeDeriv` : The derivative of a distribution on `Time × Space d` along the
  temporal coordinate.
- `distSpaceDeriv` : The derivative of a distribution on `Time × Space d` along the
  spatial `i` coordinate.
- `distSpaceGrad` : The spatial gradient of a distribution on `Time × Space d`.
- `distSpaceDiv` : The spatial divergence of a distribution on `Time × Space d`.
- `distSpaceCurl` : The spatial curl of a distribution on `Time × Space 3`.

## iii. Table of contents

- A. Derivatives involving time and space
  - A.1. Space and time derivatives in terms of curried functions
  - A.2. Commuting time and space derivatives
  - A.3. Differentiablity conditions
  - A.4. Time derivative commute with curl
  - A.5. Constant of time deriative and space derivatives zero
  - A.6. Equal up to a constant of time and space derivatives equal
- B. Derivatives of distributions on Time × Space d
  - B.1. Time derivatives
    - B.1.1. Composition with a CLM
  - B.2. Space derivatives
    - B.2.1. Space derivatives commute
    - B.2.2. Composition with a CLM
  - B.3. Time and space derivatives commute
  - B.4. The spatial gradient
  - B.5. The spatial divergence
  - B.6. The spatial curl

## iv. References

-/

@[expose] public section
namespace Space

/-!

## A. Derivatives involving time and space

-/

/-!

### A.1. Space and time derivatives in terms of curried functions

-/

lemma fderiv_space_eq_fderiv_curry {M} [NormedAddCommGroup M] [NormedSpace ℝ M]
    (f : Time → Space d → M) (t : Time) (x dx : Space d)
    (hf : Differentiable ℝ ↿f) :
    fderiv ℝ (fun x' => f t x') x dx = fderiv ℝ ↿f (t, x) (0, dx) := by
  change fderiv ℝ (↿f ∘ fun x' => (t, x')) x dx = _
  rw [fderiv_comp]
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply]
  rw [DifferentiableAt.fderiv_prodMk]
  simp only [fderiv_fun_const, Pi.zero_apply, fderiv_id', ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.zero_apply, ContinuousLinearMap.coe_id', id_eq]
  repeat' fun_prop

lemma fderiv_time_eq_fderiv_curry {M} [NormedAddCommGroup M] [NormedSpace ℝ M]
    (f : Time → Space d → M) (t dt : Time) (x : Space d)
    (hf : Differentiable ℝ ↿f) :
    fderiv ℝ (fun t' => f t' x) t dt = fderiv ℝ ↿f (t, x) (dt, 0) := by
  change fderiv ℝ (↿f ∘ fun t' => (t', x)) t dt = _
  rw [fderiv_comp]
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply]
  rw [DifferentiableAt.fderiv_prodMk]
  simp only [fderiv_id', fderiv_fun_const, Pi.zero_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.coe_id', id_eq, ContinuousLinearMap.zero_apply]
  repeat' fun_prop

/-!

### A.2. Commuting time and space derivatives

-/

/-- Derivatives along space coordinates and time commute. -/
lemma fderiv_time_commute_fderiv_space {M} [NormedAddCommGroup M] [NormedSpace ℝ M]
    (f : Time → Space d → M) (t dt : Time) (x dx : Space d)
    (hf : ContDiff ℝ 2 ↿f) :
    fderiv ℝ (fun t' => fderiv ℝ (fun x' => f t' x') x dx) t dt
    = fderiv ℝ (fun x' => fderiv ℝ (fun t' => f t' x') t dt) x dx := by
  trans fderiv ℝ (fun t' => (fderiv ℝ (↿f) (t', x) (0, dx))) t dt
  · congr
    funext t'
    apply fderiv_space_eq_fderiv_curry
    exact hf.differentiable (by simp)
  trans fderiv ℝ (fun x => (fderiv ℝ (↿f) x (0, dx))) (t, x) (dt, 0)
  · let f' : Time → Space d → M := fun t x => fderiv ℝ (↿f) (t, x) (0, dx)
    change (fderiv ℝ (fun t' => f' t' x) t) dt = _
    rw [fderiv_time_eq_fderiv_curry]
    rfl
    fun_prop
  symm
  trans fderiv ℝ (fun x' => (fderiv ℝ (↿f) (t, x') (dt, 0))) x dx
  · congr
    funext x'
    apply fderiv_time_eq_fderiv_curry
    exact hf.differentiable (by simp)
  trans fderiv ℝ (fun t => (fderiv ℝ (↿f) t (dt, 0))) (t, x) (0, dx)
  · let f'' : Time → Space d → M := fun t x => fderiv ℝ (↿f) (t, x) (dt, 0)
    change (fderiv ℝ (fun x' => f'' t x') x) dx = _
    rw [fderiv_space_eq_fderiv_curry]
    rfl
    fun_prop
  rw [fderiv_clm_apply, fderiv_clm_apply]
  simp only [fderiv_fun_const, Pi.ofNat_apply, ContinuousLinearMap.comp_zero, zero_add,
    ContinuousLinearMap.flip_apply]
  rw [IsSymmSndFDerivAt.eq]
  · apply ContDiffAt.isSymmSndFDerivAt
    apply ContDiff.contDiffAt
    exact hf
    simp
  repeat' fun_prop

lemma time_deriv_comm_space_deriv {d i} {M} [NormedAddCommGroup M] [NormedSpace ℝ M]
    {f : Time → Space d → M} (hf : ContDiff ℝ 2 ↿f) (t : Time) (x : Space d) :
    Time.deriv (fun t' => Space.deriv i (f t') x) t
    = Space.deriv i (fun x' => Time.deriv (fun t' => f t' x') t) x := by
  simp only [Time.deriv_eq, Space.deriv_eq_fderiv_basis]
  exact fderiv_time_commute_fderiv_space f t 1 x (Space.basis i) hf

/-!

### A.3. Differentiablity conditions

-/

@[fun_prop]
lemma space_deriv_differentiable_time {d i} {M} [NormedAddCommGroup M] [NormedSpace ℝ M]
    {f : Time → Space d → M} (hf : ContDiff ℝ 2 ↿f) (x : Space d) :
    Differentiable ℝ (fun t => Space.deriv i (f t) x) := by
  conv =>
    enter [2, t];
    rw [Space.deriv_eq_fderiv_basis]
  apply Differentiable.clm_apply
  · have hdd : Differentiable ℝ ↿f := hf.differentiable (by simp)
    have h1 (t : Time) : fderiv ℝ (fun x => f t x) x
      = fderiv ℝ (↿f) (t, x) ∘L (ContinuousLinearMap.inr ℝ Time (Space d)) := by
      ext w
      simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.inr_apply]
      rw [← fderiv_space_eq_fderiv_curry f t x w hdd]
    conv =>
      enter [2, y]
      change fderiv ℝ (fun x => f y x) x
      rw [h1]
    fun_prop
  · fun_prop

@[fun_prop]
lemma time_deriv_differentiable_space {d } {M} [NormedAddCommGroup M] [NormedSpace ℝ M]
    {f : Time → Space d → M} (hf : ContDiff ℝ 2 ↿f) (t : Time) :
    Differentiable ℝ (fun x => Time.deriv (f · x) t) := by
  conv =>
    enter [2, x];
    rw [Time.deriv_eq]
  apply Differentiable.clm_apply
  · have hdd : Differentiable ℝ ↿f := hf.differentiable (by simp)
    have h1 (x : Space d) : fderiv ℝ (fun t => f t x) t
      = fderiv ℝ (↿f) (t, x) ∘L (ContinuousLinearMap.inl ℝ Time (Space d)) := by
      ext w
      simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.inl_apply]
      rw [← fderiv_time_eq_fderiv_curry f t w x hdd]
    conv =>
      enter [2, t']
      change fderiv ℝ (fun x => f x t') t
      rw [h1]
    fun_prop
  · fun_prop

@[fun_prop]
lemma curl_differentiable_time
    (fₜ : Time → Space → EuclideanSpace ℝ (Fin 3))
    (hf : ContDiff ℝ 2 ↿fₜ) (x : Space) :
    Differentiable ℝ (fun t => (∇ × fₜ t) x) := by
  rw [differentiable_euclidean]
  intro i
  fin_cases i
  all_goals
    simp only [Fin.zero_eta, Fin.isValue, curl]
    fun_prop

/-!

### A.4. Time derivative commute with curl

-/
open Time

/-- Curl and time derivative commute. -/
lemma time_deriv_curl_commute (fₜ : Time → Space → EuclideanSpace ℝ (Fin 3))
    (t : Time) (x : Space) (hf : ContDiff ℝ 2 ↿fₜ) :
    ∂ₜ (fun t => (∇ × fₜ t) x) t = (∇ × fun x => (∂ₜ (fun t => fₜ t x) t)) x:= by
  ext i
  rw [← Time.deriv_euclid]
  · fin_cases i
    all_goals
    simp [curl]
    rw [Time.deriv_eq]
    rw [fderiv_fun_sub]
    simp [← Time.deriv_eq]
    rw [time_deriv_comm_space_deriv, time_deriv_comm_space_deriv]
    congr
    · funext x'
      rw [Time.deriv_euclid]
      have h1 := hf.differentiable (by simp)
      fun_prop
    · funext x'
      rw [Time.deriv_euclid]
      have h1 := hf.differentiable (by simp)
      fun_prop
    repeat' fun_prop
    · apply Differentiable.differentiableAt
      fun_prop
    · apply Differentiable.differentiableAt
      fun_prop
  · fun_prop

/-!

### A.5. Constant of time deriative and space derivatives zero

-/

lemma space_fun_of_time_deriv_eq_zero {d} {M} [NormedAddCommGroup M] [NormedSpace ℝ M]
    {f : Time → Space d → M} (hf : Differentiable ℝ ↿f)
    (h : ∀ t x, ∂ₜ (f · x) t = 0) :
    ∃ (g : Space d → M), ∀ t x, f t x = g x := by
  use fun x => f 0 x
  intro t x
  simp only
  change (fun t' => f t' x) t = (fun t' => f t' x) 0
  apply is_const_of_fderiv_eq_zero (f := fun t' => f t' x) (𝕜 := ℝ)
  · fun_prop
  intro t
  ext r
  simp only [ContinuousLinearMap.zero_apply]
  trans r.val • (fderiv ℝ (fun t' => f t' x) t) 1
  · rw [← map_smul]
    congr
    ext
    simp
  simp only [smul_eq_zero]
  right
  rw [← h t x]
  rfl

lemma time_fun_of_space_deriv_eq_zero {d} {M} [NormedAddCommGroup M] [NormedSpace ℝ M]
    {f : Time → Space d → M} (hf : Differentiable ℝ ↿f)
    (h : ∀ t x i, Space.deriv i (f t) x = 0) :
    ∃ (g : Time → M), ∀ t x, f t x = g t := by
  use fun t => f t 0
  intro t x
  simp only
  change (fun x' => f t x') x = (fun x' => f t x') 0
  apply is_const_of_fderiv_eq_zero (f := fun x' => f t x') (𝕜 := ℝ)
  · fun_prop
  intro x
  have h1 : (fderiv ℝ (fun x' => f t x') x).toLinearMap = 0 := by
    apply (Space.basis (d := d)).toBasis.ext
    intro i
    simp only [OrthonormalBasis.coe_toBasis, ContinuousLinearMap.coe_coe, LinearMap.zero_apply]
    rw [← h t x i]
    rw [Space.deriv_eq_fderiv_basis]
  ext r
  change (fderiv ℝ (fun x' => f t x') x).toLinearMap r = 0
  rw [h1]
  simp

lemma const_of_time_deriv_space_deriv_eq_zero {d} {M} [NormedAddCommGroup M] [NormedSpace ℝ M]
    {f : Time → Space d → M} (hf : Differentiable ℝ ↿f)
    (h₁ : ∀ t x, ∂ₜ (f · x) t = 0)
    (h₂ : ∀ t x i, Space.deriv i (f t) x = 0) :
    ∃ (c : M), ∀ t x, f t x = c := by
  obtain ⟨g, hg⟩ := space_fun_of_time_deriv_eq_zero hf h₁
  obtain ⟨k, hk⟩ := time_fun_of_space_deriv_eq_zero hf h₂
  use g 0
  intro t x
  have h1 : ∀ t x, g x = k t := by
    intro t x
    rw [← hg t x]
    rw [hk t x]
  rw [hk]
  rw [← h1 t 0]

/-!

### A.6. Equal up to a constant of time and space derivatives equal

-/

lemma equal_up_to_const_of_deriv_eq {d} {M} [NormedAddCommGroup M] [NormedSpace ℝ M]
    {f g : Time → Space d → M} (hf : Differentiable ℝ ↿f) (hg : Differentiable ℝ ↿g)
    (h₁ : ∀ t x, ∂ₜ (f · x) t = ∂ₜ (g · x) t)
    (h₂ : ∀ t x i, Space.deriv i (f t) x = Space.deriv i (g t) x) :
    ∃ (c : M), ∀ t x, f t x = g t x + c := by
  suffices h : ∃ c', ∀ t x, f t x - g t x = c' by
    obtain ⟨c', hc'⟩ := h
    use c'
    intro t x
    rw [← hc' t x]
    simp
  apply const_of_time_deriv_space_deriv_eq_zero
  · exact Differentiable.fun_sub hf hg
  · intro t x
    rw [Time.deriv_eq]
    rw [fderiv_fun_sub]
    simp [← Time.deriv_eq, h₁]
    · fun_prop
    · fun_prop
  · intro t x i
    rw [Space.deriv_eq_fderiv_basis]
    rw [fderiv_fun_sub]
    simp [← Space.deriv_eq_fderiv_basis, h₂]
    · fun_prop
    · fun_prop
/-!

## B. Derivatives of distributions on Time × Space d

-/

open Distribution SchwartzMap

/-!

### B.1. Time derivatives

-/

/-- The time derivative of a distribution dependent on time and space. -/
noncomputable def distTimeDeriv {M d} [NormedAddCommGroup M] [NormedSpace ℝ M] :
    ((Time × Space d) →d[ℝ] M) →ₗ[ℝ] (Time × Space d) →d[ℝ] M where
  toFun f :=
    let ev : ((Time × Space d) →L[ℝ] M) →L[ℝ] M := {
      toFun v := v (1, 0)
      map_add' v1 v2 := by
        simp only [ContinuousLinearMap.add_apply]
      map_smul' a v := by
        simp
    }
    ev.comp (Distribution.fderivD ℝ f)
  map_add' f1 f2 := by
    simp
  map_smul' a f := by simp

lemma distTimeDeriv_apply {M d} [NormedAddCommGroup M] [NormedSpace ℝ M]
    (f : (Time × Space d) →d[ℝ] M) (ε : 𝓢(Time × Space d, ℝ)) :
    (distTimeDeriv f) ε = fderivD ℝ f ε (1, 0) := by
  simp [distTimeDeriv]

lemma distTimeDeriv_apply' {M d} [NormedAddCommGroup M] [NormedSpace ℝ M]
    (f : (Time × Space d) →d[ℝ] M) (ε : 𝓢(Time × Space d, ℝ)) :
    (distTimeDeriv f) ε =
    -f (SchwartzMap.evalCLM ℝ (Time × Space d) ℝ (1, 0)
    ((fderivCLM ℝ (Time × Space d) ℝ) ε)) := by
  rw [distTimeDeriv_apply, fderivD_apply]

lemma apply_fderiv_eq_distTimeDeriv {M d} [NormedAddCommGroup M] [NormedSpace ℝ M]
    (f : (Time × Space d) →d[ℝ] M) (ε : 𝓢(Time × Space d, ℝ)) :
    f (SchwartzMap.evalCLM ℝ (Time × Space d) ℝ (1, 0) ((fderivCLM ℝ (Time × Space d) ℝ) ε)) =
    - (distTimeDeriv f) ε := by
  simp [distTimeDeriv_apply']

/-!

#### B.1.1. Composition with a CLM

-/

lemma distTimeDeriv_apply_CLM {M M2 d} [NormedAddCommGroup M] [NormedSpace ℝ M]
    [NormedAddCommGroup M2] [NormedSpace ℝ M2] (f : (Time × Space d) →d[ℝ] M)
    (c : M →L[ℝ] M2) : distTimeDeriv (c ∘L f) = c ∘L (distTimeDeriv f) := by
  ext ε
  simp [distTimeDeriv_apply, fderivD_apply]

/-!

### B.2. Space derivatives

-/

/-- The space derivative of a distribution dependent on time and space. -/
noncomputable def distSpaceDeriv {M d} [NormedAddCommGroup M] [NormedSpace ℝ M]
    (i : Fin d) : ((Time × Space d) →d[ℝ] M) →ₗ[ℝ] (Time × Space d) →d[ℝ] M where
  toFun f :=
    let ev : (Time × Space d →L[ℝ] M) →L[ℝ] M := {
      toFun v := v (0, basis i)
      map_add' v1 v2 := by
        simp only [ContinuousLinearMap.add_apply]
      map_smul' a v := by
        simp
    }
    ev.comp (Distribution.fderivD ℝ f)
  map_add' f1 f2 := by
    simp
  map_smul' a f := by simp

lemma distSpaceDeriv_apply {M d} [NormedAddCommGroup M] [NormedSpace ℝ M]
    (i : Fin d) (f : (Time × Space d) →d[ℝ] M) (ε : 𝓢(Time × Space d, ℝ)) :
    (distSpaceDeriv i f) ε = fderivD ℝ f ε (0, basis i) := by
  simp [distSpaceDeriv]

lemma distSpaceDeriv_apply' {M d} [NormedAddCommGroup M] [NormedSpace ℝ M]
    (i : Fin d) (f : (Time × Space d) →d[ℝ] M) (ε : 𝓢(Time × Space d, ℝ)) :
    (distSpaceDeriv i f) ε =
    - f ((SchwartzMap.evalCLM ℝ (Time × Space d) ℝ (0, basis i))
    ((fderivCLM ℝ (Time × Space d) ℝ) ε)) := by
  rw [distSpaceDeriv_apply, fderivD_apply]

lemma apply_fderiv_eq_distSpaceDeriv {M d} [NormedAddCommGroup M] [NormedSpace ℝ M]
    (i : Fin d) (f : (Time × Space d) →d[ℝ] M) (ε : 𝓢(Time × Space d, ℝ)) :
    f ((SchwartzMap.evalCLM ℝ (Time × Space d) ℝ (0, basis i))
    ((fderivCLM ℝ (Time × Space d) ℝ) ε)) =
    - (distSpaceDeriv i f) ε := by
  simp [distSpaceDeriv_apply']

/-!

#### B.2.1. Space derivatives commute

-/

lemma distSpaceDeriv_commute {M d} [NormedAddCommGroup M] [NormedSpace ℝ M]
    (i j : Fin d) (f : (Time × Space d) →d[ℝ] M) :
    distSpaceDeriv i (distSpaceDeriv j f) = distSpaceDeriv j (distSpaceDeriv i f) := by
  ext κ
  rw [distSpaceDeriv_apply, distSpaceDeriv_apply, fderivD_apply, fderivD_apply]
  rw [distSpaceDeriv_apply, distSpaceDeriv_apply, fderivD_apply, fderivD_apply]
  simp only [neg_neg]
  congr 1
  ext x
  change fderiv ℝ (fun x => fderiv ℝ κ x (0, basis i)) x (0, basis j) =
    fderiv ℝ (fun x => fderiv ℝ κ x (0, basis j)) x (0, basis i)
  rw [fderiv_clm_apply, fderiv_clm_apply]
  simp only [fderiv_fun_const, Pi.ofNat_apply, ContinuousLinearMap.comp_zero, zero_add,
    ContinuousLinearMap.flip_apply]
  rw [IsSymmSndFDerivAt.eq]
  · apply ContDiffAt.isSymmSndFDerivAt
    apply ContDiff.contDiffAt
    exact smooth κ ⊤
    simp only [minSmoothness_of_isRCLikeNormedField]
    exact ENat.LEInfty.out
  · have h1 := smooth κ 2
    fun_prop
  · fun_prop
  · have h1 := smooth κ 2
    fun_prop
  · fun_prop

/-!

#### B.2.2. Composition with a CLM

-/

lemma distSpaceDeriv_apply_CLM {M M2 d} [NormedAddCommGroup M] [NormedSpace ℝ M]
    [NormedAddCommGroup M2] [NormedSpace ℝ M2]
    (i : Fin d) (f : (Time × Space d) →d[ℝ] M)
    (c : M →L[ℝ] M2) : distSpaceDeriv i (c ∘L f) = c ∘L (distSpaceDeriv i f) := by
  ext ε
  simp [distSpaceDeriv_apply, fderivD_apply]

/-!

### B.3. Time and space derivatives commute

-/

lemma distTimeDeriv_commute_distSpaceDeriv {M d} [NormedAddCommGroup M] [NormedSpace ℝ M]
    (i : Fin d) (f : (Time × Space d) →d[ℝ] M) :
    distTimeDeriv (distSpaceDeriv i f) = distSpaceDeriv i (distTimeDeriv f) := by
  ext κ
  rw [distTimeDeriv_apply, distSpaceDeriv_apply, fderivD_apply, fderivD_apply]
  rw [distTimeDeriv_apply, distSpaceDeriv_apply, fderivD_apply, fderivD_apply]
  simp only [neg_neg]
  congr 1
  ext x
  change fderiv ℝ (fun x => fderiv ℝ κ x (1, 0)) x (0, basis i) =
    fderiv ℝ (fun x => fderiv ℝ κ x (0, basis i)) x (1, 0)
  rw [fderiv_clm_apply, fderiv_clm_apply]
  simp only [fderiv_fun_const, Pi.ofNat_apply, ContinuousLinearMap.comp_zero, zero_add,
    ContinuousLinearMap.flip_apply]
  rw [IsSymmSndFDerivAt.eq]
  · apply ContDiffAt.isSymmSndFDerivAt
    apply ContDiff.contDiffAt
    exact smooth κ ⊤
    simp only [minSmoothness_of_isRCLikeNormedField]
    exact ENat.LEInfty.out
  · have h1 := smooth κ 2
    fun_prop
  · fun_prop
  · have h1 := smooth κ 2
    fun_prop
  · fun_prop

/-!

### B.4. The spatial gradient

-/

/-- The spatial gradient of a distribution dependent on time and space. -/
noncomputable def distSpaceGrad {d} :
    ((Time × Space d) →d[ℝ] ℝ) →ₗ[ℝ] (Time × Space d) →d[ℝ] (EuclideanSpace ℝ (Fin d)) where
  toFun f := {
      toFun := fun ε => WithLp.toLp 2 fun i => distSpaceDeriv i f ε
      map_add' ε1 ε2 := by ext i; simp
      map_smul' a ε := by ext i; simp
      cont := by fun_prop}
  map_add' f1 f2 := by
    ext x
    simp
  map_smul' a f := by
    ext x
    simp

lemma distSpaceGrad_apply {d} (f : (Time × Space d) →d[ℝ] ℝ) (ε : 𝓢(Time × Space d, ℝ)) :
    distSpaceGrad f ε = fun i => distSpaceDeriv i f ε := by
  rfl

/-!

### B.5. The spatial divergence

-/

/-- The spatial divergence of a distribution dependent on time and space. -/
noncomputable def distSpaceDiv {d} :
    ((Time × Space d) →d[ℝ] (EuclideanSpace ℝ (Fin d))) →ₗ[ℝ] (Time × Space d) →d[ℝ] ℝ where
  toFun f := {
    toFun ε := ∑ i, distSpaceDeriv i f ε i
    map_add' ε1 ε2 := by simp [Finset.sum_add_distrib]
    map_smul' a ε := by simp [Finset.mul_sum]
    cont := by fun_prop}
  map_add' f1 f2 := by
    ext x
    simp [Finset.sum_add_distrib]
  map_smul' a f := by
    ext x
    simp [Finset.mul_sum]

lemma distSpaceDiv_apply_eq_sum_distSpaceDeriv {d}
    (f : (Time × Space d) →d[ℝ] EuclideanSpace ℝ (Fin d)) (η : 𝓢(Time ×Space d, ℝ)) :
    distSpaceDiv f η = ∑ i, distSpaceDeriv i f η i := by rfl

/-!

### B.6. The spatial curl

-/

/-- The curl of a distribution dependent on time and space. -/
noncomputable def distSpaceCurl : ((Time × Space 3) →d[ℝ] (EuclideanSpace ℝ (Fin 3))) →ₗ[ℝ]
    (Time × Space 3) →d[ℝ] (EuclideanSpace ℝ (Fin 3)) where
  toFun f :={
    toFun ε := WithLp.toLp 2 fun i =>
      match i with
      | 0 => distSpaceDeriv 2 f ε 1 - distSpaceDeriv 1 f ε 2
      | 1 => distSpaceDeriv 0 f ε 2 - distSpaceDeriv 2 f ε 0
      | 2 => distSpaceDeriv 1 f ε 0 - distSpaceDeriv 0 f ε 1
    map_add' ε1 ε2 := by
      ext i
      fin_cases i
      all_goals
        simp only [Fin.isValue, map_add, PiLp.add_apply, Fin.reduceFinMk]
        ring
    map_smul' a ε := by
      ext i
      fin_cases i
      all_goals
        simp only [Fin.isValue, map_smul, PiLp.smul_apply, smul_eq_mul, RingHom.id_apply,
          Fin.zero_eta]
        ring
    cont := by
      apply Continuous.comp
      · fun_prop
      rw [continuous_pi_iff]
      intro i
      fin_cases i <;> fun_prop
      }
  map_add' f1 f2 := by
    ext x i
    fin_cases i
    all_goals
      simp only [Fin.isValue, map_add, ContinuousLinearMap.add_apply, PiLp.add_apply, Fin.zero_eta,
        ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk]
      ring
  map_smul' a f := by
    ext x i
    fin_cases i
    all_goals
      simp only [Fin.isValue, map_smul, ContinuousLinearMap.coe_smul', Pi.smul_apply,
        PiLp.smul_apply, smul_eq_mul, Fin.reduceFinMk, ContinuousLinearMap.coe_mk',
        LinearMap.coe_mk, AddHom.coe_mk, RingHom.id_apply]
      ring

end Space
