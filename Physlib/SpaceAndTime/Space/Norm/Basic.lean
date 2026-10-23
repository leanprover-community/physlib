/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Mathematics.ForMathlib.Integration.Basic
public import Physlib.SpaceAndTime.Space.Derivatives.Laplacian
public import Physlib.SpaceAndTime.Space.Integrals.NormPow
public import Physlib.Mathematics.Distribution.PowMul
/-!

# The norm on space

## i. Overview

The main content of this file is defining `Space.normPowerSeries`, a sequence of smooth
functions which are differentiable everywhere, and which tend to the norm in the limit as `n → ∞`.

We use properties of this sequence to prove various results about distributions involving norms.

## ii. Key results

- `normPowerSeries` : A sequence of functions which are differentiable everywhere, and in the limit
  as `n → ∞` tends to `‖x‖`.
- `normPowerSeries_differentiable` : Each `normPowerSeries n` is differentiable everywhere.
- `normPowerSeries_tendsto` : `normPowerSeries n` tends to the norm in the limit as `n → ∞`.
- `distGrad_distOfFunction_norm_zpow` : The gradient of the distribution defined by a power of the
  norm.
- `distGrad_distOfFunction_log_norm` : The gradient of the distribution defined by the logarithm
  of the norm.
- `distDiv_norm_zpow_smul_repr_self_eq_smul` : The divergence of the distribution defined by
  `x ↦ ‖x‖ ^ q • x`.
- `distLaplacian_distOfFunction_norm_zpow` : The Laplacian of the distribution defined by a power
  of the norm.
- `distDiv_inv_pow_eq_dim` : The divergence of `x ↦ ‖x‖ ^ (-d) • x` equals `d * volume (ball 0 1)`
  times the Dirac delta at the origin.
- `distLaplacian_fundamentalSolution_norm_zpow` : The Laplacian of the power-form fundamental
  solution `‖x‖ ^ (2 - d)`, in every dimension (trivial at `d = 0, 2`).
- `distLaplacian_fundamentalSolution_log_norm` : The Laplacian of the two-dimensional logarithmic
  fundamental solution `Real.log ‖x‖`.

## iii. Table of contents

- A. The norm as a limit of smooth functions
  - A.1. Differentiability of the smooth approximation of the norm
  - A.2. The limit of the smooth approximation of the norm
  - A.3. The derivative of the smooth approximation of the norm
  - A.4. Limits of the derivative of the smooth approximation
  - A.5. The smooth approximation is AEStronglyMeasurable
  - A.6. Bounds on the smooth approximation of the norm
  - A.7. The `IsDistBounded` property of the smooth approximation of the norm
  - A.8. Differentiability of functions
  - A.9. Derivatives of functions
  - A.10. Gradients of distributions based on powers
    - A.10.1. The limits of gradients of distributions based on powers
  - A.11. Gradients of distributions based on logs
    - A.11.1. The limits of gradients of distributions based on logs
- B. Distributions involving norms
  - B.1. The gradient of distributions based on powers
  - B.2. The gradient of distributions based on logs
  - B.3. Divergence of radial norm-power distributions
  - B.4. The Laplacian of distributions based on powers
  - B.5. Divergence equal dirac delta
  - B.6. The Laplacian of the fundamental solution

## iv. References

* None.
-/

@[expose] public section

open SchwartzMap NNReal Physlib
noncomputable section

variable (𝕜 : Type) {E F F' : Type} [RCLike 𝕜] [NormedAddCommGroup E] [NormedAddCommGroup F]
  [NormedAddCommGroup F'] [NormedSpace ℝ E] [NormedSpace ℝ F]

namespace Space

open MeasureTheory

/-!

## A. The norm as a limit of smooth functions

-/

/-- A sequence of functions which are differentiable everywhere, and in the limit
  as `n → ∞` tends to `‖x‖`. -/
def normPowerSeries {d} : ℕ → Space d → ℝ := fun n x =>
  √(‖x‖ ^ 2 + 1/(n + 1))

lemma normPowerSeries_eq (n : ℕ) :
    normPowerSeries (d := d) n = fun x => √(‖x‖ ^ 2 + 1/(n + 1)) := rfl

lemma normPowerSeries_eq_rpow {d} (n : ℕ) :
    normPowerSeries (d := d) n = fun x => ((‖x‖ ^ 2 + 1/(n + 1))) ^ (1/2 : ℝ) :=
  funext fun _ => Real.sqrt_eq_rpow _

/-!

### A.1. Differentiability of the smooth approximation of the norm

-/

@[fun_prop]
lemma normPowerSeries_differentiable {d} (n : ℕ) :
    Differentiable ℝ (fun (x : Space d) => normPowerSeries n x) := by
  rw [normPowerSeries_eq]
  intro x
  exact ((differentiable_id.norm_sq ℝ).add_const _).differentiableAt.sqrt (by positivity)

/-!

### A.2. The limit of the smooth approximation of the norm

-/
open InnerProductSpace

open scoped Topology BigOperators FourierTransform

lemma normPowerSeries_tendsto {d} (x : Space d) :
    Filter.Tendsto (fun n => normPowerSeries n x) Filter.atTop (𝓝 (‖x‖)) := by
  have h := (Real.continuous_sqrt.tendsto _).comp
    ((tendsto_const_nhds (x := ‖x‖ ^ 2)).add (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))
  simpa only [normPowerSeries_eq, Function.comp_def, add_zero,
    Real.sqrt_sq (norm_nonneg x)] using h

lemma normPowerSeries_inv_tendsto {d} (x : Space d) (hx : x ≠ 0) :
    Filter.Tendsto (fun n => (normPowerSeries n x)⁻¹) Filter.atTop (𝓝 (‖x‖⁻¹)) :=
  (normPowerSeries_tendsto x).inv₀ (norm_ne_zero_iff.mpr hx)

/-!

### A.3. The derivative of the smooth approximation of the norm

-/
open Space

lemma deriv_normPowerSeries {d} (n : ℕ) (x : Space d) (i : Fin d) :
    ∂[i] (normPowerSeries n) x = x i * (normPowerSeries n x)⁻¹ := by
  rw [deriv_eq_fderiv_basis, normPowerSeries_eq, fderiv_sqrt]
  simp only [one_div, mul_inv_rev, fderiv_add_const, FunLike.coe_smul, Pi.smul_apply,
    smul_eq_mul]
  rw [← deriv_eq_fderiv_basis, deriv_norm_sq]
  ring
  · exact ((differentiable_id.norm_sq ℝ).add_const _).differentiableAt
  · positivity

lemma fderiv_normPowerSeries {d} (n : ℕ) (x y : Space d) :
    fderiv ℝ (fun (x : Space d) => normPowerSeries n x) x y =
      ⟪y, x⟫_ℝ * (normPowerSeries n x)⁻¹ := by
  rw [fderiv_eq_sum_deriv, inner_eq_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => by simp [deriv_normPowerSeries, mul_assoc]

/-!

### A.4. Limits of the derivative of the smooth approximation

-/

/-- The coordinate derivatives of `normPowerSeries` converge pointwise, including at zero. -/
lemma deriv_normPowerSeries_tendsto {d} (x : Space d) (i : Fin d) :
    Filter.Tendsto (fun n => ∂[i] (normPowerSeries n) x) Filter.atTop (𝓝 (x i * (‖x‖)⁻¹)) := by
  simp only [deriv_normPowerSeries]
  by_cases hx : x = 0
  · simp [hx]
  · exact tendsto_const_nhds.mul (normPowerSeries_inv_tendsto x hx)

/-- For every fixed direction, the derivatives of `normPowerSeries` converge pointwise,
including at zero. -/
lemma fderiv_normPowerSeries_tendsto {d} (x y : Space d) :
    Filter.Tendsto (fun n => fderiv ℝ (fun (x : Space d) => normPowerSeries n x) x y)
      Filter.atTop (𝓝 (⟪y, x⟫_ℝ * (‖x‖)⁻¹)) := by
  simp only [fderiv_normPowerSeries]
  by_cases hx : x = 0
  · simp [hx]
  · exact tendsto_const_nhds.mul (normPowerSeries_inv_tendsto x hx)

/-!

### A.5. The smooth approximation is AEStronglyMeasurable

-/

@[fun_prop]
lemma normPowerSeries_aestronglyMeasurable {d} (n : ℕ) :
    AEStronglyMeasurable (normPowerSeries n : Space d → ℝ) volume :=
  (normPowerSeries_differentiable n).continuous.aestronglyMeasurable

/-!

### A.6. Bounds on the smooth approximation of the norm

-/

@[simp]
lemma normPowerSeries_nonneg {d} (n : ℕ) (x : Space d) :
    0 ≤ normPowerSeries n x :=
  Real.sqrt_nonneg _

@[simp]
lemma normPowerSeries_pos {d} (n : ℕ) (x : Space d) :
    0 < normPowerSeries n x :=
  Real.sqrt_pos_of_pos (by positivity)

@[simp]
lemma normPowerSeries_ne_zero {d} (n : ℕ) (x : Space d) :
    normPowerSeries n x ≠ 0 :=
  (normPowerSeries_pos n x).ne'

lemma normPowerSeries_le_norm_sq_add_one {d} (n : ℕ) (x : Space d) :
    normPowerSeries n x ≤ ‖x‖ + 1 := by
  rw [normPowerSeries_eq]
  refine (Real.sqrt_le_left (by positivity)).mpr ?_
  have h : 1 / ((n : ℝ) + 1) ≤ 1 := div_le_one_of_le₀ (by simp) (by positivity)
  nlinarith [norm_nonneg x]

@[simp]
lemma norm_lt_normPowerSeries {d} (n : ℕ) (x : Space d) :
    ‖x‖ < normPowerSeries n x :=
  Real.lt_sqrt_of_sq_lt (lt_add_of_pos_right _ (by positivity))

lemma norm_le_normPowerSeries {d} (n : ℕ) (x : Space d) :
    ‖x‖ ≤ normPowerSeries n x :=
  (norm_lt_normPowerSeries n x).le

lemma normPowerSeries_zpow_le_norm_sq_add_one {d} (n : ℕ) (m : ℤ) (x : Space d)
    (hx : x ≠ 0) :
    (normPowerSeries n x) ^ m ≤ (‖x‖ + 1) ^ m + ‖x‖ ^ m := by
  match m with
  | .ofNat m =>
    simpa using le_add_of_le_of_nonneg
      (pow_le_pow_left₀ (by simp) (normPowerSeries_le_norm_sq_add_one n x) m) (by positivity)
  | .negSucc m =>
    simp only [zpow_negSucc]
    exact le_add_of_nonneg_of_le (by positivity) (inv_anti₀ (by positivity)
      (pow_le_pow_left₀ (by simp) (norm_le_normPowerSeries n x) (m + 1)))

lemma normPowerSeries_inv_le {d} (n : ℕ) (x : Space d) (hx : x ≠ 0) :
    (normPowerSeries n x)⁻¹ ≤ ‖x‖⁻¹ :=
  inv_anti₀ (norm_pos_iff.mpr hx) (norm_le_normPowerSeries n x)

lemma normPowerSeries_log_le_normPowerSeries {d} (n : ℕ) (x : Space d) :
    |Real.log (normPowerSeries n x)| ≤ (normPowerSeries n x)⁻¹ + (normPowerSeries n x) := by
  rw [abs_le']
  exact ⟨(Real.log_le_rpow_div (x := normPowerSeries n x) (by simp) one_pos).trans (by simp),
    (neg_le.mp (Real.neg_inv_le_log (normPowerSeries_nonneg n x))).trans
      (le_add_of_nonneg_right (normPowerSeries_nonneg n x))⟩
lemma normPowerSeries_log_le {d} (n : ℕ) (x : Space d) (hx : x ≠ 0) :
    |Real.log (normPowerSeries n x)| ≤ ‖x‖⁻¹ + (‖x‖ + 1) :=
  (normPowerSeries_log_le_normPowerSeries n x).trans
    (add_le_add (normPowerSeries_inv_le n x hx) (normPowerSeries_le_norm_sq_add_one n x))

/-!

### A.7. The `IsDistBounded` property of the smooth approximation of the norm

-/

@[fun_prop]
lemma IsDistBounded.normPowerSeries_zpow {d : ℕ} {n : ℕ} (m : ℤ) :
    IsDistBounded (d := d) (fun x => (normPowerSeries n x) ^ m) := by
  match m with
  | .ofNat m =>
    simp only [Int.ofNat_eq_natCast, zpow_natCast]
    apply IsDistBounded.mono (f := fun (x : Space d) => (‖x‖ + 1) ^ m)
    · fun_prop
    · fun_prop
    intro x
    simp only [norm_pow, Real.norm_eq_abs]
    refine pow_le_pow_left₀ (by positivity) ?_ m
    rw [abs_of_nonneg (by simp),abs_of_nonneg (by positivity)]
    exact normPowerSeries_le_norm_sq_add_one n x
  | .negSucc m =>
    simp only [zpow_negSucc]
    apply IsDistBounded.mono (f := fun (x : Space d) => ((√(1/(n + 1)) : ℝ) ^ (m + 1))⁻¹)
    · fun_prop
    · exact (((normPowerSeries_differentiable n).continuous.pow _).inv₀
        fun x => pow_ne_zero _ (normPowerSeries_ne_zero n x)).aestronglyMeasurable
    · intro x
      simp only [norm_inv, norm_pow, Real.norm_eq_abs, one_div]
      refine inv_anti₀ (by positivity) (pow_le_pow_left₀ (abs_nonneg _) ?_ _)
      rw [abs_of_nonneg (by positivity), abs_of_nonneg (by simp), normPowerSeries_eq]
      exact Real.sqrt_le_sqrt (by simp)

@[fun_prop]
lemma IsDistBounded.normPowerSeries_single {d : ℕ} {n : ℕ} :
    IsDistBounded (d := d) (fun x => (normPowerSeries n x)) := by
  simpa using IsDistBounded.normPowerSeries_zpow (n := n) (m := 1)

@[fun_prop]
lemma IsDistBounded.normPowerSeries_inv {d : ℕ} {n : ℕ} :
    IsDistBounded (d := d) (fun x => (normPowerSeries n x)⁻¹) := by
  simpa using normPowerSeries_zpow (n := n) (-1)

@[fun_prop]
lemma IsDistBounded.normPowerSeries_deriv {d : ℕ} (n : ℕ) (i : Fin d) :
    IsDistBounded (d := d) (fun x => ∂[i] (normPowerSeries n) x) := by
  simp only [deriv_normPowerSeries]
  fun_prop

@[fun_prop]
lemma IsDistBounded.normPowerSeries_fderiv {d : ℕ} (n : ℕ) (y : Space d) :
    IsDistBounded (d := d) (fun x => fderiv ℝ (fun (x : Space d) => normPowerSeries n x) x y) := by
  simp only [fderiv_eq_sum_deriv]
  exact IsDistBounded.sum_fun (by fun_prop)

@[fun_prop]
lemma IsDistBounded.normPowerSeries_log {d : ℕ} (n : ℕ) :
    IsDistBounded (d := d) (fun x => Real.log (normPowerSeries n x)) := by
  apply IsDistBounded.mono (f := fun x => (normPowerSeries n x)⁻¹ + (normPowerSeries n x))
  · fun_prop
  · exact ((normPowerSeries_differentiable n).continuous.log
      (normPowerSeries_ne_zero n)).aestronglyMeasurable
  · exact fun x => (normPowerSeries_log_le_normPowerSeries n x).trans (le_abs_self _)

/-!

### A.8. Differentiability of functions

-/

@[fun_prop]
lemma differentiable_normPowerSeries_zpow {d : ℕ} {n : ℕ} (m : ℤ) :
    Differentiable ℝ (fun x : Space d => (normPowerSeries n x) ^ m) :=
  Differentiable.zpow (by fun_prop) (.inl (normPowerSeries_ne_zero n))

@[fun_prop]
lemma differentiable_normPowerSeries_inv {d : ℕ} {n : ℕ} :
    Differentiable ℝ (fun x : Space d => (normPowerSeries n x)⁻¹) :=
  Differentiable.inv (by fun_prop) (normPowerSeries_ne_zero n)

@[fun_prop]
lemma differentiable_log_normPowerSeries {d : ℕ} {n : ℕ} :
    Differentiable ℝ (fun x : Space d => Real.log (normPowerSeries n x)) :=
  Differentiable.log (by fun_prop) (normPowerSeries_ne_zero n)
/-!

### A.9. Derivatives of functions

-/

lemma deriv_normPowerSeries_zpow {d : ℕ} {n : ℕ} (m : ℤ) (x : Space d) (i : Fin d) :
    ∂[i] (fun x : Space d => (normPowerSeries n x) ^ m) x =
      m * x i * (normPowerSeries n x) ^ (m - 2) := by
  rw [deriv_eq_fderiv_basis]
  change (fderiv ℝ ((fun x => x ^ m) ∘ normPowerSeries n) x) (basis i) = _
  rw [show m - 2 = m - 1 - 1 by ring, zpow_sub_one₀ (normPowerSeries_ne_zero n x), fderiv_comp]
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, fderiv_eq_smul_deriv, deriv_zpow',
    smul_eq_mul]
  rw [fderiv_normPowerSeries, basis_inner]
  ring
  · exact differentiableAt_zpow.mpr (.inl (normPowerSeries_ne_zero n x))
  · fun_prop

lemma fderiv_normPowerSeries_zpow {d : ℕ} {n : ℕ} (m : ℤ) (x y : Space d) :
    fderiv ℝ (fun x : Space d => (normPowerSeries n x) ^ m) x y =
      m * ⟪y, x⟫_ℝ * (normPowerSeries n x) ^ (m - 2) := by
  rw [fderiv_eq_sum_deriv, inner_eq_sum, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => by
    simp [deriv_normPowerSeries_zpow, mul_assoc, mul_comm, mul_left_comm]

lemma deriv_log_normPowerSeries {d : ℕ} {n : ℕ} (x : Space d) (i : Fin d) :
    ∂[i] (fun x : Space d => Real.log (normPowerSeries n x)) x =
      x i * (normPowerSeries n x) ^ (-2 : ℤ) := by
  rw [deriv_eq_fderiv_basis]
  change (fderiv ℝ (Real.log ∘ normPowerSeries n) x) (basis i) = _
  rw [fderiv_comp]
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, fderiv_eq_smul_deriv,
    Real.deriv_log', smul_eq_mul, Int.reduceNeg, zpow_neg]
  simp [fderiv_normPowerSeries, zpow_ofNat, sq]
  ring
  · exact Real.differentiableAt_log (normPowerSeries_ne_zero n x)
  · fun_prop

lemma fderiv_log_normPowerSeries {d : ℕ} {n : ℕ} (x y : Space d) :
    fderiv ℝ (fun x : Space d => Real.log (normPowerSeries n x)) x y =
      ⟪y, x⟫_ℝ * (normPowerSeries n x) ^ (-2 : ℤ) := by
  rw [fderiv_eq_sum_deriv, inner_eq_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => by simp [deriv_log_normPowerSeries, mul_assoc]

/-!

### A.10. Gradients of distributions based on powers

-/

lemma gradient_dist_normPowerSeries_zpow {d : ℕ} {n : ℕ} (m : ℤ) :
    ∇ᵈ (distOfFunction (fun x : Space d => (normPowerSeries n x) ^ m) (by fun_prop)) =
    distOfFunction (fun x : Space d => (m * (normPowerSeries n x) ^ (m - 2)) • basis.repr x)
    (by fun_prop) := by
  ext1 η
  refine ext_inner_right ℝ fun y => ?_
  simp [distGrad_inner_eq]
  rw [Distribution.fderivD_apply, distOfFunction_apply, distOfFunction_inner]
  calc _
    _ = - ∫ (x : Space d), fderiv ℝ η x (basis.repr.symm y) * normPowerSeries n x ^ m := by
      rfl
    _ = ∫ (x : Space d), η x * fderiv ℝ (normPowerSeries n · ^ m) x (basis.repr.symm y) := by
      rw [integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable]
      · fun_prop
      · refine IsDistBounded.integrable_space_mul ?_ η
        simp only [fderiv_normPowerSeries_zpow, mul_assoc]
        fun_prop
      · fun_prop
      · fun_prop
      · exact fun _ _ => (differentiable_normPowerSeries_zpow m).differentiableAt
    _ = ∫ (x : Space d), η x *
        (m * ⟪(basis.repr.symm y), x⟫_ℝ * (normPowerSeries n x) ^ (m - 2)) := by
      simp only [fderiv_normPowerSeries_zpow]
  congr
  funext x
  simp [inner_smul_left_eq_smul]
  left
  rw [real_inner_comm, basis_repr_inner_eq]
  ring

/-!

#### A.10.1. The limits of gradients of distributions based on powers

-/

lemma gradient_dist_normPowerSeries_zpow_tendsTo_distGrad_norm {d : ℕ} [NeZero d] (m : ℤ)
    (hm : - (d - 1 : ℕ) ≤ m) (η : 𝓢(Space d, ℝ))
    (y : EuclideanSpace ℝ (Fin d)) :
    Filter.Tendsto (fun n =>
    ⟪(∇ᵈ (distOfFunction
    (fun x : Space d => (normPowerSeries n x) ^ m) (by fun_prop))) η, y⟫_ℝ)
    Filter.atTop
    (𝓝 (⟪∇ᵈ (distOfFunction (fun x : Space d => ‖x‖ ^ m)
    (IsDistBounded.pow m hm)) η, y⟫_ℝ)) := by
  simp only [distGrad_inner_eq, Distribution.fderivD_apply, distOfFunction_apply]
  change Filter.Tendsto (fun n => - ∫ (x : Space d),
      fderiv ℝ η x (basis.repr.symm y) * normPowerSeries n x ^ m)
    Filter.atTop (𝓝 (- ∫ (x : Space d), fderiv ℝ η x (basis.repr.symm y) * ‖x‖ ^ m))
  apply Filter.Tendsto.neg
  apply MeasureTheory.tendsto_integral_of_dominated_convergence
    (bound := fun x => |fderiv ℝ η x (basis.repr.symm y)| * ((‖x‖ + 1) ^ m + ‖x‖ ^ m))
  · intro n
    exact IsDistBounded.aeStronglyMeasurable_fderiv_schwartzMap_smul (F := ℝ) (by fun_prop) η _
  · have h1 : Integrable (fun x =>
        (fderiv ℝ (⇑η) x) (basis.repr.symm y) * ((‖x‖ + 1) ^ m + ‖x‖ ^ m)) volume := by
      apply IsDistBounded.integrable_space_fderiv
        ((IsDistBounded.norm_add_pos_nat_zpow m 1 one_pos).add (IsDistBounded.pow m hm))
    refine h1.abs.congr (ae_of_all _ fun x => ?_)
    simp only [abs_mul]
    congr 1
    exact abs_of_nonneg (by positivity)
  · intro n
    filter_upwards [Measure.ae_ne volume 0] with x hx
    simp [abs_of_nonneg (normPowerSeries_nonneg n x)]
    exact mul_le_mul_of_nonneg_left
      (normPowerSeries_zpow_le_norm_sq_add_one n m x hx) (abs_nonneg _)
  · filter_upwards [Measure.ae_ne volume 0] with x hx
    exact tendsto_const_nhds.mul
      ((normPowerSeries_tendsto x).zpow₀ m (.inl (norm_ne_zero_iff.mpr hx)))

lemma gradient_dist_normPowerSeries_zpow_tendsTo {d : ℕ} [NeZero d] (m : ℤ)
    (hm : - (d - 1 : ℕ) + 1 ≤ m)
    (η : 𝓢(Space d, ℝ)) (y : EuclideanSpace ℝ (Fin d)) :
    Filter.Tendsto (fun n =>
    ⟪(∇ᵈ (distOfFunction (fun x : Space d => (normPowerSeries n x) ^ m)
    (by fun_prop))) η, y⟫_ℝ)
    Filter.atTop
    (𝓝 (⟪distOfFunction (fun x : Space d => (m * ‖x‖ ^ (m - 2)) • basis.repr x) (by
    simp [← smul_smul]
    refine IsDistBounded.const_fun_smul ?_ ↑m
    apply IsDistBounded.zpow_smul_repr_self
    omega) η, y⟫_ℝ)) := by
  simp only [gradient_dist_normPowerSeries_zpow]
  simp [distOfFunction_inner]
  have h1 (n : ℕ) (x : Space d) :
    η x * ⟪(↑m * normPowerSeries n x ^ (m - 2)) • basis.repr x, (y)⟫_ℝ =
    η x * (m * (⟪basis.repr x, y⟫_ℝ * (normPowerSeries n x) ^ (m - 2))) := by
    rw [real_inner_smul_left]
    ring
  simp only [h1]
  apply MeasureTheory.tendsto_integral_of_dominated_convergence
    (bound := fun x => |η x| * |m| * |⟪basis.repr x, y⟫_ℝ| * ((‖x‖ + 1) ^ (m - 2) + ‖x‖ ^ (m - 2)))
  · intro n
    apply IsDistBounded.aeStronglyMeasurable_schwartzMap_smul (F := ℝ) ?_ η
    apply IsDistBounded.const_mul_fun
    simp [basis_repr_inner_eq]
    exact IsDistBounded.isDistBounded_mul_inner' (by fun_prop) _
  · have h1 : Integrable (fun x =>
        η x * (m * (⟪basis.repr x, y⟫_ℝ * ((‖x‖ + 1) ^ (m - 2) + ‖x‖ ^ (m - 2))))) volume := by
      apply IsDistBounded.integrable_space_mul ?_ η
      apply IsDistBounded.const_mul_fun
      simp [mul_add]
      apply IsDistBounded.add
      · simp [basis_repr_inner_eq]
        exact IsDistBounded.isDistBounded_mul_inner'
          (IsDistBounded.norm_add_pos_nat_zpow (m - 2) 1 one_pos) _
      · simp [basis_repr_inner_eq]
        conv =>
          enter [1, x]
          rw [real_inner_comm]
        apply IsDistBounded.isDistBounded_mul_inner_of_smul_norm
        · apply IsDistBounded.mono (f := fun x => ‖x‖ ^ (m - 1) + 1)
          · exact (IsDistBounded.pow (m - 1) (by omega)).add (by fun_prop)
          · exact AEMeasurable.aestronglyMeasurable (by fun_prop)
          · intro x
            simp only [norm_mul, Real.norm_eq_abs, abs_norm, norm_zpow]
            rw [abs_of_nonneg (by positivity)]
            by_cases hx : x = 0
            · subst hx
              simp [zero_zpow_eq]
              split_ifs <;> grind
            · rw [mul_comm, ← zpow_add_one₀ (norm_ne_zero_iff.mpr hx),
                show m - 2 + 1 = m - 1 by ring]
              simp
        · exact AEMeasurable.aestronglyMeasurable (by fun_prop)
    refine h1.abs.congr (ae_of_all _ fun x => ?_)
    simp only [abs_mul, mul_assoc, Int.cast_abs,
      abs_of_nonneg (show (0:ℝ) ≤ (‖x‖ + 1) ^ (m - 2) + ‖x‖ ^ (m - 2) by positivity)]
  · intro n
    filter_upwards [Measure.ae_ne volume 0] with x hx
    simp [mul_assoc]
    gcongr
    rw [abs_of_nonneg (by simp)]
    exact normPowerSeries_zpow_le_norm_sq_add_one n (m - 2) x hx
  · filter_upwards [Measure.ae_ne volume 0] with x hx
    have h2 : ⟪((m : ℝ) * ‖x‖ ^ (m - 2)) • basis.repr x, y⟫_ℝ =
        (m : ℝ) * (⟪basis.repr x, y⟫_ℝ * ‖x‖ ^ (m - 2)) := by
      rw [real_inner_smul_left]
      ring
    rw [h2]
    exact tendsto_const_nhds.mul (tendsto_const_nhds.mul (tendsto_const_nhds.mul
      ((normPowerSeries_tendsto x).zpow₀ _ (.inl (norm_ne_zero_iff.mpr hx)))))

/-!

### A.11. Gradients of distributions based on logs

-/

lemma gradient_dist_normPowerSeries_log {d : ℕ} {n : ℕ} :
    ∇ᵈ (distOfFunction (fun x : Space d => Real.log (normPowerSeries n x)) (by fun_prop)) =
    distOfFunction (fun x : Space d => ((normPowerSeries n x) ^ (- 2 : ℤ)) • basis.repr x)
    (by fun_prop) := by
  ext1 η
  refine ext_inner_right ℝ fun y => ?_
  simp [distGrad_inner_eq]
  rw [Distribution.fderivD_apply, distOfFunction_apply, distOfFunction_inner]
  calc _
    _ = - ∫ (x : Space d), fderiv ℝ η x (basis.repr.symm y) * Real.log (normPowerSeries n x) := by
      rfl
    _ = ∫ (x : Space d), η x *
        fderiv ℝ (fun x => Real.log (normPowerSeries n x)) x (basis.repr.symm y) := by
      rw [integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable]
      · fun_prop
      · refine IsDistBounded.integrable_space_mul ?_ η
        simp only [fderiv_log_normPowerSeries]
        fun_prop
      · fun_prop
      · fun_prop
      · exact fun _ _ => Differentiable.differentiableAt (by fun_prop)
    _ = ∫ (x : Space d), η x * (⟪basis.repr.symm y, x⟫_ℝ * (normPowerSeries n x) ^ (- 2 : ℤ)) := by
      simp only [fderiv_log_normPowerSeries]
  congr
  funext x
  simp [inner_smul_left_eq_smul]
  left
  rw [real_inner_comm, basis_repr_inner_eq]
  ring

/-!

#### A.11.1. The limits of gradients of distributions based on logs

-/

lemma gradient_dist_normPowerSeries_log_tendsTo_distGrad_norm {d : ℕ} (hd : 2 ≤ d)
    (η : 𝓢(Space d, ℝ)) (y : EuclideanSpace ℝ (Fin d)) :
    Filter.Tendsto (fun n =>
    ⟪(∇ᵈ (distOfFunction
    (fun x : Space d => Real.log (normPowerSeries n x)) (by fun_prop))) η, y⟫_ℝ)
    Filter.atTop
    (𝓝 (⟪∇ᵈ (distOfFunction (fun x : Space d => Real.log ‖x‖)
    (IsDistBounded.log_norm)) η, y⟫_ℝ)) := by
  have : NeZero d := ⟨by omega⟩
  simp only [distGrad_inner_eq, Distribution.fderivD_apply, distOfFunction_apply]
  change Filter.Tendsto (fun n => -
    ∫ (x : Space d), fderiv ℝ η x (basis.repr.symm y) * Real.log (normPowerSeries n x))
    Filter.atTop (𝓝 (- ∫ (x : Space d), fderiv ℝ η x (basis.repr.symm y) * Real.log ‖x‖))
  apply Filter.Tendsto.neg
  apply MeasureTheory.tendsto_integral_of_dominated_convergence
    (bound := fun x => |fderiv ℝ η x (basis.repr.symm y)| * (‖x‖⁻¹ + (‖x‖ + 1)))
  · intro n
    exact IsDistBounded.aeStronglyMeasurable_fderiv_schwartzMap_smul (F := ℝ) (by fun_prop) η _
  · have h1 : Integrable (fun x => (fderiv ℝ (⇑η) x) (basis.repr.symm y) *
        (‖x‖⁻¹ + (‖x‖ + 1))) volume := by
      apply IsDistBounded.integrable_space_fderiv
        (IsDistBounded.add IsDistBounded.inv (by fun_prop))
    refine h1.abs.congr (ae_of_all _ fun x => ?_)
    simp only [abs_mul]
    congr 1
    exact abs_of_nonneg (by positivity)
  · intro n
    filter_upwards [Measure.ae_ne volume 0] with x hx
    simp only [norm_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (normPowerSeries_log_le n x hx) (abs_nonneg _)
  · filter_upwards [Measure.ae_ne volume 0] with x hx
    exact tendsto_const_nhds.mul
      ((normPowerSeries_tendsto x).log (norm_ne_zero_iff.mpr hx))

lemma gradient_dist_normPowerSeries_log_tendsTo {d : ℕ} (hd : 2 ≤ d)
    (η : 𝓢(Space d, ℝ)) (y : EuclideanSpace ℝ (Fin d)) :
    Filter.Tendsto (fun n =>
    ⟪(∇ᵈ (distOfFunction (fun x : Space d => Real.log (normPowerSeries n x))
    (by fun_prop))) η, y⟫_ℝ)
    Filter.atTop
    (𝓝 (⟪distOfFunction (fun x : Space d => (‖x‖ ^ (- 2 : ℤ)) • basis.repr x) (by
    refine (IsDistBounded.zpow_smul_repr_self _ ?_)
    omega) η, y⟫_ℝ)) := by
  have : NeZero d := ⟨by omega⟩
  simp only [gradient_dist_normPowerSeries_log, distOfFunction_inner]
  have h1 (n : ℕ) (x : Space d) :
    η x * ⟪(normPowerSeries n x ^ (- 2 : ℤ)) • basis.repr x, y⟫_ℝ =
    η x * ((⟪basis.repr x, y⟫_ℝ * (normPowerSeries n x) ^ (- 2 : ℤ))) := by
    rw [real_inner_smul_left]
    ring
  simp only [h1]
  apply MeasureTheory.tendsto_integral_of_dominated_convergence
    (bound := fun x => |η x| * |⟪basis.repr x, y⟫_ℝ| * ((‖x‖ + 1) ^ (- 2 : ℤ) + ‖x‖ ^ (- 2 : ℤ)))
  · intro n
    refine IsDistBounded.aeStronglyMeasurable_schwartzMap_smul (F := ℝ) ?_ η
    simp only [basis_repr_inner_eq]
    exact IsDistBounded.isDistBounded_mul_inner' (by fun_prop) _
  · have h1 : Integrable (fun x =>
        η x * ((⟪basis.repr x, y⟫_ℝ * ((‖x‖ + 1) ^ (- 2 : ℤ) + ‖x‖ ^ (- 2 : ℤ))))) volume := by
      apply IsDistBounded.integrable_space_mul ?_ η
      simp [mul_add]
      apply IsDistBounded.add
      · simp only [basis_repr_inner_eq]
        exact IsDistBounded.isDistBounded_mul_inner'
          (IsDistBounded.norm_add_pos_nat_zpow (- 2) 1 one_pos) _
      · simp only [basis_repr_inner_eq]
        convert IsDistBounded.mul_inner_pow_neg_two (basis.repr.symm y) using 1
        funext x
        simp [real_inner_comm]
    refine h1.abs.congr (ae_of_all _ fun x => ?_)
    simp only [abs_mul, mul_assoc,
      abs_of_nonneg (show (0:ℝ) ≤ (‖x‖ + 1) ^ (- 2 : ℤ) + ‖x‖ ^ (- 2 : ℤ) by positivity)]
  · intro n
    filter_upwards [Measure.ae_ne volume 0] with x hx
    simp [mul_assoc]
    gcongr
    simpa using normPowerSeries_zpow_le_norm_sq_add_one n (- 2 : ℤ) x hx
  · filter_upwards [Measure.ae_ne volume 0] with x hx
    have h2 : ⟪(‖x‖ ^ (- 2 : ℤ)) • basis.repr x, y⟫_ℝ =
        ⟪basis.repr x, y⟫_ℝ * ‖x‖ ^ (- 2 : ℤ) := by
      rw [real_inner_smul_left]
      ring
    rw [h2]
    exact tendsto_const_nhds.mul (tendsto_const_nhds.mul
      ((normPowerSeries_tendsto x).zpow₀ _ (.inl (norm_ne_zero_iff.mpr hx))))

/-!

## B. Distributions involving norms

-/

/-!

### B.1. The gradient of distributions based on powers

-/

lemma distGrad_distOfFunction_norm_zpow {d : ℕ} [NeZero d]
    (m : ℤ) (hm : - (d - 1 : ℕ) + 1 ≤ m) :
    ∇ᵈ (distOfFunction (fun x : Space d => ‖x‖ ^ m)
      (IsDistBounded.pow m (by omega)))
    = distOfFunction (fun x : Space d => (m * ‖x‖ ^ (m - 2)) • basis.repr x) (by
      simp [← smul_smul]
      refine IsDistBounded.const_fun_smul ?_ ↑m
      apply IsDistBounded.zpow_smul_repr_self
      omega) := by
  ext1 η
  exact ext_inner_right ℝ fun y => tendsto_nhds_unique
    (gradient_dist_normPowerSeries_zpow_tendsTo_distGrad_norm m (by omega) η y)
    (gradient_dist_normPowerSeries_zpow_tendsTo m hm η y)

/-!

### B.2. The gradient of distributions based on logs

-/

lemma distGrad_distOfFunction_log_norm {d : ℕ} (hd : 2 ≤ d := by omega) :
    ∇ᵈ (distOfFunction (fun x : Space d => Real.log ‖x‖)
      (IsDistBounded.log_norm))
    = distOfFunction (fun x : Space d => (‖x‖ ^ (- 2 : ℤ)) • basis.repr x) (by
      refine (IsDistBounded.zpow_smul_repr_self _ ?_)
      omega) := by
  ext1 η
  exact ext_inner_right ℝ fun y => tendsto_nhds_unique
    (gradient_dist_normPowerSeries_log_tendsTo_distGrad_norm hd η y)
    (gradient_dist_normPowerSeries_log_tendsTo hd η y)

/-!

### B.3. Divergence of radial norm-power distributions

-/
open Distribution

private lemma integrable_real_pow_mul_schwartz
    (ψ : 𝓢(ℝ, ℝ)) (k : ℕ) :
    Integrable (fun x : ℝ => x ^ k * ψ x) volume := by
  refine (ψ.integrable_pow_mul volume k).mono' (by fun_prop)
    (ae_of_all _ fun x => by simp [norm_mul, norm_pow])

set_option backward.isDefEq.respectTransparency false in
private lemma radial_power_deriv_integral_by_parts
    {d : ℕ} (η : 𝓢(Space d, ℝ))
    (n : ↑(Metric.sphere (0 : Space d) 1))
    (p : ℕ) (hp : 0 < p) :
    - ∫ (r : Set.Ioi (0 : ℝ)),
        r.1 ^ p * (_root_.deriv (fun a => η (a • n.1)) r.1)
        ∂(.comap Subtype.val volume)
      =
      (p : ℝ) * ∫ (r : Set.Ioi (0 : ℝ)),
        r.1 ^ (p - 1) * η (r.1 • n.1)
        ∂(.comap Subtype.val volume) := by
  let η' : 𝓢(ℝ, ℝ) := SchwartzMap.compCLM (g := fun a => a • n.1) ℝ (by
    apply And.intro
    · fun_prop
    · intro n'
      match n' with
      | 0 =>
        use 1, 1
        simp [norm_smul]
      | 1 =>
        use 0, 1
        intro x
        simp [fderiv_smul_const]
      | n' + 1 + 1 =>
        use 0, 0
        intro x
        simp only [Real.norm_eq_abs, pow_zero, mul_one, norm_le_zero_iff]
        rw [iteratedFDeriv_succ_eq_comp_right]
        conv_lhs =>
          enter [2, 3, y]
          simp [fderiv_smul_const]
        rw [iteratedFDeriv_succ_const]
        rfl) (by use 1, 1; simp [norm_smul]) η
  have hη'_apply (x : ℝ) : η' x = η (x • n.1) := by
    simp [η']
  have hmul_iter_apply :
      ∀ k x, ((Physlib.Distribution.powOneMul ℝ)^[k] η') x = x ^ k * η' x := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      intro x
      rw [Function.iterate_succ_apply', Physlib.Distribution.powOneMul_apply, ih, pow_succ]
      change x * (x ^ k * η' x) = x ^ k * x * η' x
      ring
  have hleft_subtype :
      ∫ (r : Set.Ioi (0 : ℝ)),
          r.1 ^ p * _root_.deriv (fun a => η (a • n.1)) r.1
          ∂(.comap Subtype.val volume)
        =
        ∫ (x : ℝ) in Set.Ioi (0 : ℝ),
          x ^ p * _root_.deriv (fun a => η (a • n.1)) x :=
    MeasureTheory.integral_subtype_comap measurableSet_Ioi
      fun x : ℝ => x ^ p * _root_.deriv (fun a => η (a • n.1)) x
  have hright_subtype :
      ∫ (r : Set.Ioi (0 : ℝ)),
          r.1 ^ (p - 1) * η (r.1 • n.1)
          ∂(.comap Subtype.val volume)
        =
        ∫ (x : ℝ) in Set.Ioi (0 : ℝ),
          x ^ (p - 1) * η (x • n.1) :=
    MeasureTheory.integral_subtype_comap measurableSet_Ioi fun x : ℝ => x ^ (p - 1) * η (x • n.1)
  rw [hleft_subtype, hright_subtype]
  have hIBP :
      ∫ (x : ℝ) in Set.Ioi (0 : ℝ),
          x ^ p * _root_.deriv (fun a => η (a • n.1)) x
        =
        (0 : ℝ) - (0 : ℝ) -
          ∫ (x : ℝ) in Set.Ioi (0 : ℝ),
            ((p : ℝ) * x ^ (p - 1)) * η (x • n.1) := by
    refine MeasureTheory.integral_Ioi_mul_deriv_eq_deriv_mul
      (a := (0 : ℝ))
      (u := fun x : ℝ => x ^ p)
      (u' := fun x : ℝ => (p : ℝ) * x ^ (p - 1))
      (v := fun x : ℝ => η (x • n.1))
      (v' := fun x : ℝ => _root_.deriv (fun a => η (a • n.1)) x)
      (a' := (0 : ℝ)) (b' := (0 : ℝ)) ?_ ?_ ?_ ?_ ?_ ?_
    · exact fun x _ => by simpa using hasDerivAt_pow p x
    · exact fun x _ => DifferentiableAt.hasDerivAt (by fun_prop)
    · refine (integrable_real_pow_mul_schwartz ((SchwartzMap.derivCLM ℝ ℝ) η')
        p).integrableOn.congr_fun (fun x _ => ?_) measurableSet_Ioi
      have hderiv_eq : _root_.deriv η' x = _root_.deriv (fun a => η (a • n.1)) x := by congr 1
      simp [SchwartzMap.derivCLM_apply, hderiv_eq]
    · refine ((integrable_real_pow_mul_schwartz η' (p - 1)).const_mul
        (p : ℝ)).integrableOn.congr_fun (fun x _ => ?_) measurableSet_Ioi
      ring_nf
      simp [hη'_apply, mul_assoc]
    · have hcont : ContinuousAt (fun x : ℝ => x ^ p * η (x • n.1)) (0 : ℝ) := by fun_prop
      have hlim := tendsto_nhdsWithin_of_tendsto_nhds (s := Set.Ioi (0 : ℝ)) hcont.tendsto
      simp only [ne_eq, hp.ne', not_false_eq_true, zero_pow, zero_smul, zero_mul] at hlim
      exact hlim
    · have hsch : Filter.Tendsto (fun x : ℝ => ((Physlib.Distribution.powOneMul ℝ)^[p] η') x)
          Filter.atTop (𝓝 (0 : ℝ)) :=
        Filter.Tendsto.mono_left
          (((Physlib.Distribution.powOneMul ℝ)^[p] η').toZeroAtInfty.zero_at_infty')
          atTop_le_cocompact
      exact hsch.congr' (Filter.Eventually.of_forall (hmul_iter_apply p))
  calc
    -∫ (x : ℝ) in Set.Ioi (0 : ℝ),
        x ^ p * _root_.deriv (fun a => η (a • n.1)) x
        = ∫ (x : ℝ) in Set.Ioi (0 : ℝ),
            ((p : ℝ) * x ^ (p - 1)) * η (x • n.1) := by
          rw [hIBP]
          ring
    _ = (p : ℝ) * ∫ (x : ℝ) in Set.Ioi (0 : ℝ),
          x ^ (p - 1) * η (x • n.1) := by
          simp only [mul_assoc, integral_const_mul]

private lemma distDiv_norm_zpow_smul_repr_self_apply_eq_radial_deriv
    {d p : ℕ} [NeZero d] (q : ℤ) (hq : 0 < q + (d : ℤ))
    (hp_int : (p : ℤ) = q + (d : ℤ))
    (η : 𝓢(Space d, ℝ)) :
    (∇ᵈ ⬝ (distOfFunction (fun x : Space d => ‖x‖ ^ q • basis.repr x)
      (IsDistBounded.zpow_smul_repr_self q (by omega)))) η =
      - ∫ n, (∫ (r : Set.Ioi (0 : ℝ)),
        r.1 ^ p * (_root_.deriv (fun a => η (a • n.1)) r.1)
        ∂(.comap Subtype.val volume))
        ∂(volume (α := Space d).toSphere) := by
  let F : Space d → ℝ := fun x =>
    inner ℝ (‖x‖ ^ q • basis.repr x) (grad η x)
  calc
    (∇ᵈ ⬝ (distOfFunction (fun x : Space d => ‖x‖ ^ q • basis.repr x)
      (IsDistBounded.zpow_smul_repr_self q (by omega)))) η
        = - ∫ x, F x := by
            rw [distDiv_ofFunction]
    _ = - ∫ r, F (r.2.1 • r.1.1)
        ∂(volume (α := Space d).toSphere.prod
          (Measure.volumeIoiPow (Module.finrank ℝ (Space d) - 1))) := by
          rw [integral_volume_eq_spherical]
    _ = - ∫ n, (∫ r, F (r.1 • n.1)
        ∂(Measure.volumeIoiPow (Module.finrank ℝ (Space d) - 1)))
        ∂(volume (α := Space d).toSphere) := by
          rw [MeasureTheory.integral_prod]
          exact integrable_isDistBounded_inner_grad_schwartzMap_spherical
            (IsDistBounded.zpow_smul_repr_self q (by omega)) η
    _ = - ∫ n, (∫ (r : Set.Ioi (0 : ℝ)),
        r.1 ^ p * (_root_.deriv (fun a => η (a • n.1)) r.1)
        ∂(.comap Subtype.val volume))
        ∂(volume (α := Space d).toSphere) := by
          congr
          funext n
          simp [F, Measure.volumeIoiPow]
          rw [Integration.integral_withDensity_ofReal_eq_integral_smul]
          congr
          funext r
          have hr : 0 < (r : ℝ) := r.2
          have hnorm := norm_smul_sphere n (le_of_lt hr)
          simp only [smul_eq_mul]
          rw [hnorm, ← grad_smul_inner_space (n : Space d) (⇑η)
            (SchwartzMap.differentiable η) (r : ℝ) hr, real_inner_comm]
          simp only [inner_smul_right]
          rw [← radial_jacobian_zpow_mul_self hp_int hr]
          ring
          · fun_prop
          intro r
          exact pow_nonneg r.2.le _

lemma distDiv_norm_zpow_smul_repr_self_eq_smul
    {d : ℕ} [NeZero d] (q : ℤ) (hq : 0 < q + (d : ℤ)) :
    ∇ᵈ ⬝ (distOfFunction (fun x : Space d => ‖x‖ ^ q • basis.repr x)
      (IsDistBounded.zpow_smul_repr_self q (by omega))) =
      (((q + d : ℤ) : ℝ) •
        distOfFunction (fun x : Space d => ‖x‖ ^ q)
          (IsDistBounded.pow q (by omega))) := by
  ext η
  let p : ℕ := Int.toNat (q + (d : ℤ))
  have hp_int : (p : ℤ) = q + (d : ℤ) := by simpa [p] using Int.toNat_of_nonneg (le_of_lt hq)
  have hp_pos : 0 < p := by omega
  have hcoef : (((q + d : ℤ) : ℝ)) = (p : ℝ) := by
    exact_mod_cast hp_int.symm
  calc
    (∇ᵈ ⬝ (distOfFunction (fun x : Space d => ‖x‖ ^ q • basis.repr x)
      (IsDistBounded.zpow_smul_repr_self q (by omega)))) η
        = - ∫ n, (∫ (r : Set.Ioi (0 : ℝ)),
            r.1 ^ p * (_root_.deriv (fun a => η (a • n.1)) r.1)
            ∂(.comap Subtype.val volume))
            ∂(volume (α := Space d).toSphere) := by
          exact distDiv_norm_zpow_smul_repr_self_apply_eq_radial_deriv q hq hp_int η
    _ = ∫ n, (p : ℝ) * ∫ (r : Set.Ioi (0 : ℝ)),
            r.1 ^ (p - 1) * η (r.1 • n.1)
            ∂(.comap Subtype.val volume)
            ∂(volume (α := Space d).toSphere) := by
          rw [← integral_neg]
          congr
          funext n
          exact radial_power_deriv_integral_by_parts η n p hp_pos
    _ = (p : ℝ) * ∫ n : ↑(Metric.sphere (0 : Space d) 1),
          ∫ (r : Set.Ioi (0 : ℝ)),
            r.1 ^ (p - 1) * η (r.1 • n.1)
            ∂(.comap Subtype.val volume)
            ∂(volume (α := Space d).toSphere) := by
          rw [integral_const_mul]
    _ = (p : ℝ) * ∫ x : Space d, η x * ‖x‖ ^ q := by
          rw [← radial_norm_power_spherical_integral_eq_space_integral hp_int hp_pos η]
    _ = (((q + (d : ℤ) : ℤ) : ℝ) •
        distOfFunction (fun x : Space d => ‖x‖ ^ q)
          (IsDistBounded.pow q (by omega))) η := by
          simp [distOfFunction_apply, hcoef]

/-!

### B.4. The Laplacian of distributions based on powers

-/

lemma distLaplacian_distOfFunction_norm_zpow {d : ℕ} [NeZero d] (m : ℤ)
    (hdiv : 0 < m - 2 + (d : ℤ)) :
    Δᵈ (distOfFunction (fun x : Space d => ‖x‖ ^ m)
      (IsDistBounded.pow m (by omega))) =
      (((m : ℝ) * (((m - 2 + d : ℤ) : ℝ))) •
        distOfFunction (fun x : Space d => ‖x‖ ^ (m - 2))
          (IsDistBounded.pow (m - 2) (by omega))) := by
  rw [distLaplacian, LinearMap.comp_apply, distGrad_distOfFunction_norm_zpow m (by omega)]
  have hdist :
      distOfFunction (fun x : Space d => (m * ‖x‖ ^ (m - 2)) • basis.repr x)
          (by
            simp [← smul_smul]
            refine IsDistBounded.const_fun_smul ?_ ↑m
            apply IsDistBounded.zpow_smul_repr_self
            omega) =
        (m : ℝ) • distOfFunction
          (fun x : Space d => ‖x‖ ^ (m - 2) • basis.repr x)
          (IsDistBounded.zpow_smul_repr_self (m - 2) (by omega)) := by
    convert distOfFunction_smul_fun
      (fun x : Space d => ‖x‖ ^ (m - 2) • basis.repr x)
      (IsDistBounded.zpow_smul_repr_self (m - 2) (by omega)) (m : ℝ) using 1
    ext x
    simp [smul_smul]
  rw [hdist, map_smul, distDiv_norm_zpow_smul_repr_self_eq_smul (m - 2) hdiv, smul_smul]

/-!

### B.5. Divergence equal dirac delta

We show that the divergence of `x ↦ ‖x‖ ^ (- d) • x` is equal to a multiple of the Dirac delta
at `0`.

-/

/-- The distributional divergence of the radial field `x ↦ ‖x‖ ^ (-d) • x` (i.e. `x / ‖x‖ ^ d`)
equals `d * volume (Metric.ball 0 1)` — the surface area of the unit sphere `S^{d-1}` — times the
Dirac delta at the origin. This is the Gauss-law identity underlying the fundamental solution of
the Laplacian: away from `0` the field is divergence-free, and all of its flux concentrates at the
origin. -/
lemma distDiv_inv_pow_eq_dim {d : ℕ} [NeZero d] :
    ∇ᵈ ⬝ (distOfFunction (fun x : Space d => ‖x‖ ^ (- d : ℤ) • basis.repr x)
      (IsDistBounded.zpow_smul_repr_self (- d : ℤ) (by omega))) =
      (d * (volume (α := Space d)).real (Metric.ball 0 1)) • diracDelta ℝ 0 := by
  ext η
  calc _
      _ = - ∫ x, ⟪‖x‖⁻¹ ^ d • basis.repr x, Space.grad η x⟫_ℝ := by
          simp only [zpow_neg, zpow_natCast, distDiv_ofFunction, inv_pow]
      _ = - ∫ x, ‖x‖⁻¹ ^ (d - 1) * ⟪‖x‖⁻¹ • basis.repr x, Space.grad η x⟫_ℝ := by
          simp only [← pow_sub_one_mul (NeZero.ne d), inv_pow, inner_smul_left, conj_trivial,
            map_inv₀, neg_inj]
          ring_nf
      _ = - ∫ x, ‖x‖⁻¹ ^ (d - 1) * (_root_.deriv (fun a => η (a • ‖x‖⁻¹ • x)) ‖x‖) := by
          simp only [real_inner_comm,
            ← grad_inner_space_unit_vector _ _ (SchwartzMap.differentiable η)]
      _ = - ∫ r, ‖r.2.1‖⁻¹ ^ (d - 1) * (_root_.deriv (fun a => η (a • r.1)) ‖r.2.1‖)
        ∂(volume (α := Space d).toSphere.prod
        (Measure.volumeIoiPow (Module.finrank ℝ (Space d) - 1))) := by
          rw [← MeasureTheory.MeasurePreserving.integral_comp (f := homeomorphUnitSphereProd _)
            (MeasureTheory.Measure.measurePreserving_homeomorphUnitSphereProd
            (volume (α := Space d)))
            (Homeomorph.measurableEmbedding (homeomorphUnitSphereProd (Space d)))]
          congr 1
          simp only [inv_pow, homeomorphUnitSphereProd_apply_snd_coe, norm_norm,
            homeomorphUnitSphereProd_apply_fst_coe]
          let f (x : Space d) : ℝ :=
            (‖↑x‖ ^ (d - 1))⁻¹ * _root_.deriv (fun a => η (a • ‖↑x‖⁻¹ • ↑x)) ‖↑x‖
          conv_rhs =>
            enter [2, x]
            change f x.1
          rw [MeasureTheory.integral_subtype_comap (by simp), ← setIntegral_univ]
          change ∫ x in Set.univ, f x = ∫ (x : Space d) in _, f x
          exact setIntegral_congr_set (MeasureTheory.ae_eq_univ.mpr (by simp)).symm
      _ = - ∫ n, (∫ r, ‖r.1‖⁻¹ ^ (d - 1) *
        (_root_.deriv (fun a => η (a • n)) ‖r.1‖)
        ∂((Measure.volumeIoiPow (Module.finrank ℝ (Space d) - 1))))
        ∂(volume (α := Space d).toSphere) := by
          rw [MeasureTheory.integral_prod]
          /- Integrable condition. -/
          convert integrable_isDistBounded_inner_grad_schwartzMap_spherical
            (IsDistBounded.inv_pow_smul_repr_self (d) (by omega)) η
          rename_i r
          simp only [Real.norm_eq_abs, inv_pow, Function.comp_apply,
            homeomorphUnitSphereProd_symm_apply_coe, map_smul]
          let x : Space d := r.2.1 • r.1.1
          have hr : (0 : ℝ) < r.2.1 := r.2.2
          rw [abs_of_nonneg (le_of_lt hr)]
          trans (r.2.1 ^ (d - 1))⁻¹ * _root_.deriv (fun a => η (a • ‖↑x‖⁻¹ • ↑x)) ‖x‖
          · simp [x, norm_smul]
            left
            congr
            funext a
            congr
            simp [smul_smul]
            rw [abs_of_nonneg (le_of_lt hr)]
            field_simp
            simp only [one_smul]
            rw [abs_of_nonneg (le_of_lt hr)]
          rw [← grad_inner_space_unit_vector, real_inner_comm, ← pow_sub_one_mul (NeZero.ne d)]
          simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (le_of_lt hr),
            norm_eq_of_mem_sphere, mul_one, map_smul, inner_smul_left, map_inv₀, conj_trivial,
            mul_inv_rev, x]
          field_simp
          exact SchwartzMap.differentiable η
      _ = - ∫ n, (∫ (r : Set.Ioi (0 : ℝ)),
        (_root_.deriv (fun a => η (a • n)) r.1) ∂(.comap Subtype.val volume))
        ∂(volume (α := Space d).toSphere) := by
          congr
          funext n
          simp [Measure.volumeIoiPow]
          rw [Integration.integral_withDensity_ofReal_eq_integral_smul]
          congr
          funext r
          have hr : (0 : ℝ) < r.1 := r.2
          rw [abs_of_nonneg hr.le, smul_eq_mul,
            ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero (d - 1) hr.ne'), one_mul]
          · fun_prop
          intro r
          exact pow_nonneg r.2.le _
      _ = - ∫ n, (-η 0) ∂(volume (α := Space d).toSphere) := by
          congr
          funext n
          let η' (n : ↑(Metric.sphere 0 1)) : 𝓢(ℝ, ℝ) := compCLM (g := fun a => a • n.1) ℝ (by
            apply And.intro
            · fun_prop
            · intro n'
              match n' with
              | 0 =>
                use 1, 1
                simp [norm_smul]
              | 1 =>
                use 0, 1
                intro x
                simp [fderiv_smul_const]
              | n' + 1 + 1 =>
                use 0, 0
                intro x
                simp only [Real.norm_eq_abs, pow_zero, mul_one, norm_le_zero_iff]
                rw [iteratedFDeriv_succ_eq_comp_right]
                conv_lhs =>
                  enter [2, 3, y]
                  simp [fderiv_smul_const]
                rw [iteratedFDeriv_succ_const]
                rfl) (by use 1, 1; simp [norm_smul]) η
          rw [MeasureTheory.integral_subtype_comap (by simp),
            MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto (f := fun a => η (a • n)) (m := 0)]
          · simp
          · exact ContinuousAt.continuousWithinAt (by fun_prop)
          · exact fun x _ => DifferentiableAt.hasDerivAt (by fun_prop)
          · exact (integrable ((derivCLM ℝ ℝ) (η' n))).integrableOn
          · exact Filter.Tendsto.mono_left (η' n).toZeroAtInfty.zero_at_infty' atTop_le_cocompact
      _ = η 0 * (d * (volume (α := Space d)).real (Metric.ball 0 1)) := by
          simp only [integral_const, Measure.toSphere_real_apply_univ, finrank_eq_dim, smul_eq_mul,
            mul_neg, neg_neg]
          ring
  simp only [_root_.smul_apply, diracDelta_apply, smul_eq_mul]
  ring

/-!

### B.6. The Laplacian of the fundamental solution

-/

/-- The distributional Laplacian of `‖x‖ ^ (2 - d)` is `(2 - d) * d * volume (Metric.ball 0 1)`
times the Dirac delta at the origin. For `d ≥ 3` this `‖x‖ ^ (2 - d)` is the (singular)
fundamental solution of the Laplacian, and for `d = 1` it is `‖x‖`. When `d = 2` the exponent
vanishes, so the identity collapses to the trivial `Δᵈ 1 = 0`; the genuine two-dimensional
fundamental solution is the logarithm, proved in `distLaplacian_fundamentalSolution_log_norm`.
The statement also holds vacuously for `d = 0`, where the space is trivial. -/
lemma distLaplacian_fundamentalSolution_norm_zpow {d : ℕ} :
    Δᵈ (distOfFunction (fun x : Space d => ‖x‖ ^ (- ((d : ℤ) - 2)))
      (IsDistBounded.pow _ (by omega))) =
      ((- ((d : ℝ) - 2)) * d *
        (volume (α := Space d)).real (Metric.ball 0 1)) • diracDelta ℝ 0 := by
  by_cases h : d = 0
  · subst h
    have hzero :
        distOfFunction (fun x : Space 0 => ‖x‖ ^ 2)
          (IsDistBounded.pow _ (by omega)) = 0 := by
      ext η
      rw [distOfFunction_apply]
      refine integral_eq_zero_of_ae (ae_of_all _ fun x => ?_)
      rw [Subsingleton.elim x 0]
      simp
    simp only [Nat.cast_zero, zero_sub, neg_neg]
    rw [hzero]
    simp
  · have : NeZero d := ⟨by omega⟩
    rw [distLaplacian]
    change ∇ᵈ ⬝ (∇ᵈ (distOfFunction
      (fun x : Space d => ‖x‖ ^ (- ((d : ℤ) - 2)))
      (IsDistBounded.pow (- ((d : ℤ) - 2)) (by omega)))) = _
    rw [distGrad_distOfFunction_norm_zpow (- ((d : ℤ) - 2)) (by omega)]
    simp only [neg_sub, Int.cast_sub, Int.cast_ofNat, Int.cast_natCast, sub_sub_cancel_left]
    have hdist :
        distOfFunction
          (fun x : Space d =>
            ((2 - (d : ℝ)) * ‖x‖ ^ (- (d : ℤ))) • basis.repr x)
          (by
            simpa [smul_smul] using
              (IsDistBounded.const_fun_smul
                (F := EuclideanSpace ℝ (Fin d))
                (IsDistBounded.zpow_smul_repr_self (- (d : ℤ)) (by omega))
                (2 - (d : ℝ)))) =
          (2 - (d : ℝ)) • distOfFunction
            (fun x : Space d =>
              ‖x‖ ^ (- (d : ℤ)) • basis.repr x)
            (IsDistBounded.zpow_smul_repr_self (- (d : ℤ)) (by omega)) := by
      convert distOfFunction_smul_fun
        (fun x : Space d =>
          ‖x‖ ^ (- (d : ℤ)) • basis.repr x)
        (IsDistBounded.zpow_smul_repr_self (- (d : ℤ)) (by omega))
        (2 - (d : ℝ)) using 1
      ext x
      simp [smul_smul]
    rw [hdist, map_smul, distDiv_inv_pow_eq_dim, smul_smul]
    ring_nf

/-- In dimension two the fundamental solution of the Laplacian is the logarithm: the
distributional Laplacian of `Real.log ‖x‖` is `2 * volume (Metric.ball 0 1)` times the Dirac
delta at the origin. -/
lemma distLaplacian_fundamentalSolution_log_norm :
    Δᵈ (distOfFunction (fun x : Space 2 => Real.log ‖x‖) IsDistBounded.log_norm) =
      (2 * (volume (α := Space 2)).real (Metric.ball 0 1)) • diracDelta ℝ 0 := by
  rw [distLaplacian]
  change ∇ᵈ ⬝ (∇ᵈ (distOfFunction (fun x : Space 2 => Real.log ‖x‖)
    IsDistBounded.log_norm)) = _
  rw [distGrad_distOfFunction_log_norm (by norm_num)]
  simpa only [Nat.cast_ofNat] using distDiv_inv_pow_eq_dim (d := 2)

end Space
