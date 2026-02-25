/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.SpaceAndTime.Space.Derivatives.Div
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Analysis.Calculus.FDeriv.Norm
/-!

# The norm on space

## i. Overview

The main content of this file is defining `Space.normPowerSeries`, a power series which is
differentiable everywhere, and which tends to the norm in the limit as `n → ∞`.

We use properties of this power series to prove various results about distributions involving norms.

## ii. Key results

- `normPowerSeries` : A power series which is differentiable everywhere, and in the limit
  as `n → ∞` tends to `‖x‖`.
- `normPowerSeries_differentiable` : The power series is differentiable everywhere.
- `normPowerSeries_tendsto` : The power series tends to the norm in the limit as `n → ∞`.
- `distGrad_distOfFunction_norm_zpow` : The gradient of the distribution defined by a power of the
  norm.
- `distGrad_distOfFunction_log_norm` : The gradient of the distribution defined by the logarithm
  of the norm.
- `distDiv_inv_pow_eq_dim` : The divergence of the distribution defined by the
  inverse power of the norm proportional to the Dirac delta distribution.

## iii. Table of contents

- A. The norm as a power series
  - A.1. Differentiability of the norm power series
  - A.2. The limit of the norm power series
  - A.3. The derivative of the norm power series
  - A.4. Limits of the derivative of the power series
  - A.5. The power series is AEStronglyMeasurable
  - A.6. Bounds on the norm power series
  - A.7. The `IsDistBounded` property of the norm power series
  - A.8. Differentiability of functions
  - A.9. Derivatives of functions
  - A.10. Gradients of distributions based on powers
    - A.10.1. The limits of gradients of distributions based on powers
  - A.11. Gradients of distributions based on logs
    - A.11.1. The limits of gradients of distributions based on logs
- B. Distributions involving norms
  - B.1. The gradient of distributions based on powers
  - B.2. The gradient of distributions based on logs
  - B.3. Divergence equal dirac delta

## iv. References

-/
open SchwartzMap NNReal
noncomputable section

variable (𝕜 : Type) {E F F' : Type} [RCLike 𝕜] [NormedAddCommGroup E] [NormedAddCommGroup F]
  [NormedAddCommGroup F'] [NormedSpace ℝ E] [NormedSpace ℝ F]

namespace Space

open MeasureTheory

/-!

## A. The norm as a power series

-/

/-- A power series which is differentiable everywhere, and in the limit
  as `n → ∞` tends to `‖x‖`. -/
def normPowerSeries {d} : ℕ → Space d → ℝ := fun n x =>
  √(‖x‖ ^ 2 + 1/(n + 1))

lemma normPowerSeries_eq (n : ℕ) :
    normPowerSeries (d := d) n = fun x => √(‖x‖ ^ 2 + 1/(n + 1)) := rfl

lemma normPowerSeries_eq_rpow {d} (n : ℕ) :
    normPowerSeries (d := d) n = fun x => ((‖x‖ ^ 2 + 1/(n + 1))) ^ (1/2 : ℝ) := by
  rw [normPowerSeries_eq]
  funext x
  rw [← Real.sqrt_eq_rpow]

/-!

### A.1. Differentiability of the norm power series

-/

@[fun_prop]
lemma normPowerSeries_differentiable {d} (n : ℕ) :
    Differentiable ℝ (fun (x : Space d) => normPowerSeries n x) := by
  rw [normPowerSeries_eq_rpow]
  refine Differentiable.rpow_const ?_ ?_
  · refine (Differentiable.fun_add_iff_right ?_).mpr ?_
    · apply Differentiable.norm_sq ℝ
      fun_prop
    · fun_prop
  · intro x
    have h1 : 0 < ‖x‖ ^ 2 + 1 / (↑n + 1) := by positivity
    grind

/-!

### A.2. The limit of the norm power series

-/
open InnerProductSpace

open scoped Topology BigOperators FourierTransform

lemma normPowerSeries_tendsto {d} (x : Space d) (hx : x ≠ 0) :
    Filter.Tendsto (fun n => normPowerSeries n x) Filter.atTop (𝓝 (‖x‖)) := by
  conv => enter [1, n]; rw [normPowerSeries_eq_rpow]
  simp only [one_div]
  have hx_norm : ‖x‖ = (‖x‖ ^ 2 + 0) ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow]
    simp
  conv_rhs => rw [hx_norm]
  refine Filter.Tendsto.rpow ?_ ?_ ?_
  · apply Filter.Tendsto.add
    · exact tendsto_const_nhds
    · simpa using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  · simp
  · left
    simpa using hx

lemma normPowerSeries_inv_tendsto {d} (x : Space d) (hx : x ≠ 0) :
    Filter.Tendsto (fun n => (normPowerSeries n x)⁻¹) Filter.atTop (𝓝 (‖x‖⁻¹)) := by
  apply Filter.Tendsto.inv₀
  · exact normPowerSeries_tendsto x hx
  · simpa using hx

/-!

### A.3. The derivative of the norm power series

-/
open Space

lemma deriv_normPowerSeries {d} (n : ℕ) (x : Space d) (i : Fin d) :
    ∂[i] (normPowerSeries n) x = x i * (normPowerSeries n x)⁻¹ := by
  rw [deriv_eq_fderiv_basis]
  rw [normPowerSeries_eq]
  rw [fderiv_sqrt]
  simp only [one_div, mul_inv_rev, fderiv_add_const, ContinuousLinearMap.coe_smul', Pi.smul_apply,
    smul_eq_mul]
  rw [← deriv_eq_fderiv_basis]
  rw [deriv_norm_sq]
  ring
  · simp
    apply DifferentiableAt.norm_sq ℝ
    fun_prop
  · positivity

lemma fderiv_normPowerSeries {d} (n : ℕ) (x y : Space d) :
    fderiv ℝ (fun (x : Space d) => normPowerSeries n x) x y =
      ⟪y, x⟫_ℝ * (normPowerSeries n x)⁻¹ := by
  rw [fderiv_eq_sum_deriv, inner_eq_sum, Finset.sum_mul]
  congr
  funext i
  simp [deriv_normPowerSeries]
  ring

/-!

### A.4. Limits of the derivative of the power series

-/

lemma deriv_normPowerSeries_tendsto {d} (x : Space d) (hx : x ≠ 0) (i : Fin d) :
    Filter.Tendsto (fun n => ∂[i] (normPowerSeries n) x) Filter.atTop (𝓝 (x i * (‖x‖)⁻¹)) := by
  conv => enter [1, n]; rw [deriv_normPowerSeries]
  refine Filter.Tendsto.mul ?_ ?_
  · exact tendsto_const_nhds
  · exact normPowerSeries_inv_tendsto x hx

lemma fderiv_normPowerSeries_tendsto {d} (x y : Space d) (hx : x ≠ 0) :
    Filter.Tendsto (fun n => fderiv ℝ (fun (x : Space d) => normPowerSeries n x) x y)
      Filter.atTop (𝓝 (⟪y, x⟫_ℝ * (‖x‖)⁻¹)) := by
  conv => enter [1, n]; rw [fderiv_normPowerSeries]
  refine Filter.Tendsto.mul ?_ ?_
  · exact tendsto_const_nhds
  · exact normPowerSeries_inv_tendsto x hx

/-!

### A.5. The power series is AEStronglyMeasurable

-/

@[fun_prop]
lemma normPowerSeries_aestronglyMeasurable {d} (n : ℕ) :
    AEStronglyMeasurable (normPowerSeries n : Space d → ℝ) volume := by
  rw [normPowerSeries_eq_rpow]
  refine StronglyMeasurable.aestronglyMeasurable ?_
  refine stronglyMeasurable_iff_measurable.mpr ?_
  fun_prop

/-!

### A.6. Bounds on the norm power series

-/

@[simp]
lemma normPowerSeries_nonneg {d} (n : ℕ) (x : Space d) :
    0 ≤ normPowerSeries n x := by
  rw [normPowerSeries_eq]
  simp

@[simp]
lemma normPowerSeries_pos {d} (n : ℕ) (x : Space d) :
    0 < normPowerSeries n x := by
  rw [normPowerSeries_eq]
  simp only [one_div, Real.sqrt_pos]
  positivity

@[simp]
lemma normPowerSeries_ne_zero {d} (n : ℕ) (x : Space d) :
    normPowerSeries n x ≠ 0 := by
  rw [normPowerSeries_eq]
  simp only [one_div, ne_eq]
  positivity

lemma normPowerSeries_le_norm_sq_add_one {d} (n : ℕ) (x : Space d) :
    normPowerSeries n x ≤ ‖x‖ + 1 := by
  trans √(‖x‖ ^ 2 + 1)
  · rw [normPowerSeries_eq]
    apply Real.sqrt_le_sqrt
    simp only [one_div, add_le_add_iff_left]
    refine inv_le_one_iff₀.mpr ?_
    right
    simp
  · refine (Real.sqrt_le_left (by positivity)).mpr ?_
    trans (‖x‖ ^ 2 + 1) + (2 * ‖x‖)
    · simp
    · ring_nf
      rfl

@[simp]
lemma norm_lt_normPowerSeries {d} (n : ℕ) (x : Space d) :
    ‖x‖ < normPowerSeries n x := by
  rw [normPowerSeries_eq]
  apply Real.lt_sqrt_of_sq_lt
  simp only [one_div, lt_add_iff_pos_right, inv_pos]
  positivity

lemma norm_le_normPowerSeries {d} (n : ℕ) (x : Space d) :
    ‖x‖ ≤ normPowerSeries n x := by
  rw [normPowerSeries_eq]
  apply Real.le_sqrt_of_sq_le
  simp only [one_div, le_add_iff_nonneg_right, inv_nonneg]
  positivity

lemma normPowerSeries_zpow_le_norm_sq_add_one {d} (n : ℕ) (m : ℤ) (x : Space d)
    (hx : x ≠ 0) :
    (normPowerSeries n x) ^ m ≤ (‖x‖ + 1) ^ m + ‖x‖ ^ m := by
  match m with
  | .ofNat m =>
    trans (‖x‖ + 1) ^ m
    · simp
      refine pow_le_pow_left₀ (by simp) ?_ m
      exact normPowerSeries_le_norm_sq_add_one n x
    · simp
  | .negSucc m =>
    trans (‖x‖ ^ (m + 1))⁻¹; swap
    · simp
      positivity
    simp only [zpow_negSucc]
    refine inv_anti₀ ?_ ?_
    · positivity
    refine pow_le_pow_left₀ (by simp) ?_ (m + 1)
    exact norm_le_normPowerSeries n x

lemma normPowerSeries_inv_le {d} (n : ℕ) (x : Space d) (hx : x ≠ 0) :
    (normPowerSeries n x)⁻¹ ≤ ‖x‖⁻¹ := by
  refine inv_anti₀ ?_ ?_
  · positivity
  apply Real.le_sqrt_of_sq_le
  simp only [one_div, le_add_iff_nonneg_right, inv_nonneg]
  positivity

lemma normPowerSeries_log_le_normPowerSeries {d} (n : ℕ) (x : Space d) :
    |Real.log (normPowerSeries n x)| ≤ (normPowerSeries n x)⁻¹ + (normPowerSeries n x) := by
  have h1 := Real.neg_inv_le_log (x := (normPowerSeries n x)) (by simp)
  have h2 := Real.log_le_rpow_div (x := (normPowerSeries n x)) (by simp) (ε := 1) (by positivity)
  simp_all
  rw [abs_le']
  generalize Real.log ‖x‖ = r at *
  apply And.intro
  · apply h2.trans
    simp
  · rw [neg_le]
    apply le_trans _ h1
    simp
lemma normPowerSeries_log_le {d} (n : ℕ) (x : Space d) (hx : x ≠ 0) :
    |Real.log (normPowerSeries n x)| ≤ ‖x‖⁻¹ + (‖x‖ + 1) := by
  apply le_trans (normPowerSeries_log_le_normPowerSeries n x) ?_
  apply add_le_add
  · exact normPowerSeries_inv_le n x hx
  · exact normPowerSeries_le_norm_sq_add_one n x

/-!

### A.7. The `IsDistBounded` property of the norm power series

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
    · rw [normPowerSeries_eq_rpow]
      refine StronglyMeasurable.aestronglyMeasurable ?_
      refine stronglyMeasurable_iff_measurable.mpr ?_
      fun_prop
    · intro x
      simp only [norm_inv, norm_pow, Real.norm_eq_abs, one_div]
      refine inv_anti₀ (by positivity) ?_
      refine (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by simp)).mpr ?_
      rw [abs_of_nonneg (by positivity), abs_of_nonneg (by simp)]
      rw [normPowerSeries_eq]
      simp only [Real.sqrt_inv, one_div]
      rw [← Real.sqrt_inv]
      apply Real.sqrt_le_sqrt
      simp

@[fun_prop]
lemma IsDistBounded.normPowerSeries_single {d : ℕ} {n : ℕ} :
    IsDistBounded (d := d) (fun x => (normPowerSeries n x)) := by
  convert IsDistBounded.normPowerSeries_zpow (n := n) (m := 1) using 1
  simp

@[fun_prop]
lemma IsDistBounded.normPowerSeries_inv {d : ℕ} {n : ℕ} :
    IsDistBounded (d := d) (fun x => (normPowerSeries n x)⁻¹) := by
  convert normPowerSeries_zpow (n := n) (-1) using 1
  simp

@[fun_prop]
lemma IsDistBounded.normPowerSeries_deriv {d : ℕ} (n : ℕ) (i : Fin d) :
    IsDistBounded (d := d) (fun x => ∂[i] (normPowerSeries n) x) := by
  conv =>
    enter [1, x];
    rw [deriv_normPowerSeries]
  fun_prop

@[fun_prop]
lemma IsDistBounded.normPowerSeries_fderiv {d : ℕ} (n : ℕ) (y : Space d) :
    IsDistBounded (d := d) (fun x => fderiv ℝ (fun (x : Space d) => normPowerSeries n x) x y) := by
  conv =>
    enter [1, x];
    rw [fderiv_eq_sum_deriv]
  apply IsDistBounded.sum_fun
  fun_prop

@[fun_prop]
lemma IsDistBounded.normPowerSeries_log {d : ℕ} (n : ℕ) :
    IsDistBounded (d := d) (fun x => Real.log (normPowerSeries n x)) := by
  apply IsDistBounded.mono (f := fun x => (normPowerSeries n x)⁻¹ + (normPowerSeries n x))
  · fun_prop
  · apply AEMeasurable.aestronglyMeasurable
    fun_prop
  · intro x
    simp only [Real.norm_eq_abs]
    conv_rhs => rw [abs_of_nonneg (by
      apply add_nonneg
      · simp
      · simp)]
    exact normPowerSeries_log_le_normPowerSeries n x

/-!

### A.8. Differentiability of functions

-/

@[fun_prop]
lemma differentiable_normPowerSeries_zpow {d : ℕ} {n : ℕ} (m : ℤ) :
    Differentiable ℝ (fun x : Space d => (normPowerSeries n x) ^ m) := by
  refine Differentiable.zpow ?_ ?_
  · fun_prop
  · left
    exact normPowerSeries_ne_zero n

@[fun_prop]
lemma differentiable_normPowerSeries_inv {d : ℕ} {n : ℕ} :
    Differentiable ℝ (fun x : Space d => (normPowerSeries n x)⁻¹) := by
  convert differentiable_normPowerSeries_zpow (n := n) (m := -1) using 1
  funext x
  simp

@[fun_prop]
lemma differentiable_log_normPowerSeries {d : ℕ} {n : ℕ} :
    Differentiable ℝ (fun x : Space d => Real.log (normPowerSeries n x)) := by
  refine Differentiable.log ?_ ?_
  · fun_prop
  · intro x
    exact normPowerSeries_ne_zero n x
/-!

### A.9. Derivatives of functions

-/

lemma deriv_normPowerSeries_zpow {d : ℕ} {n : ℕ} (m : ℤ) (x : Space d) (i : Fin d) :
    ∂[i] (fun x : Space d => (normPowerSeries n x) ^ m) x =
      m * x i * (normPowerSeries n x) ^ (m - 2) := by
  rw [deriv_eq_fderiv_basis]
  change (fderiv ℝ ((fun x => x ^ m) ∘ normPowerSeries n) x) (basis i) = _
  rw [fderiv_comp]
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, fderiv_eq_smul_deriv, deriv_zpow',
    smul_eq_mul]
  rw [fderiv_normPowerSeries]
  simp only [basis_inner]
  field_simp
  ring_nf
  have h1 : normPowerSeries n x ^ (-1 + m) = normPowerSeries n x ^ ((-2 + m) + 1) := by
    ring_nf
  rw [h1, zpow_add₀]
  simp only [Int.reduceNeg, zpow_one]
  ring
  · simp
  · refine DifferentiableAt.zpow ?_ ?_
    · fun_prop
    · left
      exact normPowerSeries_ne_zero n x
  · fun_prop

lemma fderiv_normPowerSeries_zpow {d : ℕ} {n : ℕ} (m : ℤ) (x y : Space d) :
    fderiv ℝ (fun x : Space d => (normPowerSeries n x) ^ m) x y =
      m * ⟪y, x⟫_ℝ * (normPowerSeries n x) ^ (m - 2) := by
  rw [fderiv_eq_sum_deriv, inner_eq_sum, Finset.mul_sum, Finset.sum_mul]
  congr
  funext i
  simp [deriv_normPowerSeries_zpow]
  ring

lemma deriv_log_normPowerSeries {d : ℕ} {n : ℕ} (x : Space d) (i : Fin d) :
    ∂[i] (fun x : Space d => Real.log (normPowerSeries n x)) x =
      x i * (normPowerSeries n x) ^ (-2 : ℤ) := by
  rw [deriv_eq_fderiv_basis]
  change (fderiv ℝ (Real.log ∘ normPowerSeries n) x) (basis i) = _
  rw [fderiv_comp,]
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, fderiv_eq_smul_deriv,
    Real.deriv_log', smul_eq_mul, Int.reduceNeg, zpow_neg]
  rw [fderiv_normPowerSeries]
  simp [zpow_ofNat, sq]
  ring
  · apply DifferentiableAt.log ?_ ?_
    · fun_prop
    exact normPowerSeries_ne_zero n x
  · fun_prop

lemma fderiv_log_normPowerSeries {d : ℕ} {n : ℕ} (x y : Space d) :
    fderiv ℝ (fun x : Space d => Real.log (normPowerSeries n x)) x y =
      ⟪y, x⟫_ℝ * (normPowerSeries n x) ^ (-2 : ℤ) := by
  rw [fderiv_eq_sum_deriv, inner_eq_sum, Finset.sum_mul]
  congr
  funext i
  simp [deriv_log_normPowerSeries]
  ring

/-!

### A.10. Gradients of distributions based on powers

-/

lemma gradient_dist_normPowerSeries_zpow {d : ℕ} {n : ℕ} (m : ℤ) :
    distGrad (distOfFunction (fun x : Space d => (normPowerSeries n x) ^ m) (by fun_prop)) =
    distOfFunction (fun x : Space d => (m * (normPowerSeries n x) ^ (m - 2)) • basis.repr x)
    (by fun_prop) := by
  ext1 η
  apply ext_inner_right ℝ
  intro y
  simp [distGrad_inner_eq]
  rw [Distribution.fderivD_apply, distOfFunction_apply, distOfFunction_inner]
  calc _
    _ = - ∫ (x : Space d), fderiv ℝ η x (basis.repr.symm y) * normPowerSeries n x ^ m := by
      rfl
    _ = ∫ (x : Space d), η x * fderiv ℝ (normPowerSeries n · ^ m) x (basis.repr.symm y) := by
      rw [integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable]
      · fun_prop
      · refine IsDistBounded.integrable_space_mul ?_ η
        conv => enter [1, x]; rw [fderiv_normPowerSeries_zpow]
        simp [mul_assoc]
        fun_prop
      · fun_prop
      · exact η.differentiable
      · fun_prop
    _ = ∫ (x : Space d), η x *
        (m * ⟪(basis.repr.symm y), x⟫_ℝ * (normPowerSeries n x) ^ (m - 2)) := by
      congr
      funext x
      rw [fderiv_normPowerSeries_zpow]
  congr
  funext x
  simp [inner_smul_left_eq_smul]
  left
  rw [real_inner_comm, basis_repr_inner_eq]
  ring

/-!

#### A.10.1. The limits of gradients of distributions based on powers

-/

lemma gradient_dist_normPowerSeries_zpow_tendsTo_distGrad_norm {d : ℕ} (m : ℤ)
    (hm : - (d.succ - 1 : ℕ) ≤ m) (η : 𝓢(Space d.succ, ℝ))
    (y : EuclideanSpace ℝ (Fin d.succ)) :
    Filter.Tendsto (fun n =>
    ⟪(distGrad (distOfFunction
    (fun x : Space d.succ => (normPowerSeries n x) ^ m) (by fun_prop))) η, y⟫_ℝ)
    Filter.atTop
    (𝓝 (⟪distGrad (distOfFunction (fun x : Space d.succ => ‖x‖ ^ m)
    (IsDistBounded.pow m hm)) η, y⟫_ℝ)) := by
  simp only [distGrad_inner_eq, Distribution.fderivD_apply, distOfFunction_apply]
  change Filter.Tendsto (fun n => - ∫ (x : Space d.succ),
      fderiv ℝ η x (basis.repr.symm y) * normPowerSeries n x ^ m)
    Filter.atTop (𝓝 (- ∫ (x : Space d.succ), fderiv ℝ η x (basis.repr.symm y) * ‖x‖ ^ m))
  apply Filter.Tendsto.neg
  apply MeasureTheory.tendsto_integral_of_dominated_convergence
    (bound := fun x => |fderiv ℝ η x (basis.repr.symm y)| * ((‖x‖ + 1) ^ m + ‖x‖ ^ m))
  · intro n
    apply IsDistBounded.aeStronglyMeasurable_fderiv_schwartzMap_smul (F := ℝ) ?_
    fun_prop
  · have h1 : Integrable (fun x =>
        (fderiv ℝ (⇑η) x) (basis.repr.symm y) * ((‖x‖ + 1) ^ m + ‖x‖ ^ m)) volume := by
      apply IsDistBounded.integrable_space_fderiv ?_
      apply IsDistBounded.add
      · refine IsDistBounded.norm_add_pos_nat_zpow m 1 ?_
        simp
      · exact IsDistBounded.pow m hm
    rw [← integrable_norm_iff] at h1
    convert h1 using 1
    funext x
    simp only [Nat.succ_eq_add_one, norm_mul, Real.norm_eq_abs, mul_eq_mul_left_iff, abs_eq_zero]
    left
    rw [abs_of_nonneg (by positivity)]
    fun_prop
  · intro n
    rw [Filter.eventually_iff_exists_mem]
    use {0}ᶜ
    constructor
    · rw [compl_mem_ae_iff, measure_singleton]
    intro x hx
    simp at hx
    simp
    apply mul_le_mul (by rfl) _ (by positivity) (by positivity)
    rw [abs_of_nonneg (by simp)]
    exact normPowerSeries_zpow_le_norm_sq_add_one n m x hx
  · rw [Filter.eventually_iff_exists_mem]
    use {0}ᶜ
    constructor
    · rw [compl_mem_ae_iff, measure_singleton]
    intro x hx
    apply Filter.Tendsto.mul
    · exact tendsto_const_nhds
    have h1 : Filter.Tendsto (fun x_1 => normPowerSeries x_1 x ^ (m : ℝ))
      Filter.atTop (𝓝 (‖x‖ ^ (m : ℝ))) := by
      refine Filter.Tendsto.rpow ?_ ?_ ?_
      · apply normPowerSeries_tendsto x hx
      · simp
      · left
        simpa using hx
    simpa using h1

lemma gradient_dist_normPowerSeries_zpow_tendsTo {d : ℕ} (m : ℤ) (hm : - (d.succ - 1 : ℕ) + 1 ≤ m)
    (η : 𝓢(Space d.succ, ℝ)) (y : EuclideanSpace ℝ (Fin d.succ)) :
    Filter.Tendsto (fun n =>
    ⟪(distGrad (distOfFunction (fun x : Space d.succ => (normPowerSeries n x) ^ m)
    (by fun_prop))) η, y⟫_ℝ)
    Filter.atTop
    (𝓝 (⟪distOfFunction (fun x : Space d.succ => (m * ‖x‖ ^ (m - 2)) • basis.repr x) (by
    simp [← smul_smul]
    refine IsDistBounded.const_fun_smul ?_ ↑m
    apply IsDistBounded.zpow_smul_repr_self
    simp_all
    grind) η, y⟫_ℝ)) := by
  conv =>
    enter [1, n];
    rw [gradient_dist_normPowerSeries_zpow]
  simp [distOfFunction_inner]
  have h1 (n : ℕ) (x : Space d.succ) :
    η x * ⟪(↑m * normPowerSeries n x ^ (m - 2)) • basis.repr x, (y)⟫_ℝ =
    η x * (m * (⟪basis.repr x, y⟫_ℝ * (normPowerSeries n x) ^ (m - 2))) := by
    simp [inner_smul_left]
    ring_nf
    left
    trivial

  conv =>
    enter [1, n, 2, x];
    rw [h1 n x]
  apply MeasureTheory.tendsto_integral_of_dominated_convergence
    (bound := fun x => |η x| * |m| * |⟪basis.repr x, y⟫_ℝ| * ((‖x‖ + 1) ^ (m - 2) + ‖x‖ ^ (m - 2)))
  · intro n
    apply IsDistBounded.aeStronglyMeasurable_schwartzMap_smul (F := ℝ) ?_ η
    apply IsDistBounded.const_mul_fun
    simp [basis_repr_inner_eq]
    apply IsDistBounded.isDistBounded_mul_inner'
    fun_prop
  · have h1 : Integrable (fun x =>
        η x * (m * (⟪basis.repr x, y⟫_ℝ * ((‖x‖ + 1) ^ (m - 2) + ‖x‖ ^ (m - 2))))) volume := by
      apply IsDistBounded.integrable_space_mul ?_ η
      apply IsDistBounded.const_mul_fun
      simp [mul_add]
      apply IsDistBounded.add
      · simp [basis_repr_inner_eq]
        apply IsDistBounded.isDistBounded_mul_inner'
        refine IsDistBounded.norm_add_pos_nat_zpow (m - 2) 1 ?_
        simp
      · simp [basis_repr_inner_eq]
        conv =>
          enter [1, x]
          rw [real_inner_comm]
        apply IsDistBounded.isDistBounded_mul_inner_of_smul_norm
        · apply IsDistBounded.mono (f := fun x => ‖x‖ ^ (m - 1) + 1)
          · apply IsDistBounded.add
            · apply IsDistBounded.pow (m - 1)
              simp_all
            · fun_prop
          · apply AEMeasurable.aestronglyMeasurable
            fun_prop
          · intro x
            simp only [norm_mul, Real.norm_eq_abs, abs_norm, norm_zpow]
            rw [abs_of_nonneg (by positivity)]
            by_cases hx : x = 0
            · subst hx
              simp [zero_zpow_eq]
              split_ifs <;> grind
            · trans ‖x‖ ^ (m - 1); swap
              · simp
              apply le_of_eq
              trans ‖x‖ ^ (m - 2 + 1)
              rw [zpow_add₀, zpow_one]
              ring
              simpa using hx
              ring_nf
        · apply AEMeasurable.aestronglyMeasurable
          fun_prop
    rw [← integrable_norm_iff] at h1
    convert h1 using 1
    funext x
    simp [mul_assoc]
    rw [abs_of_nonneg (by positivity)]
    simp only [true_or]
    fun_prop
  · intro n
    rw [Filter.eventually_iff_exists_mem]
    use {0}ᶜ
    constructor
    · rw [compl_mem_ae_iff, measure_singleton]
    intro x hx
    simp at hx
    simp [mul_assoc]
    apply mul_le_mul (by rfl) _ (by positivity) (by positivity)
    apply mul_le_mul (by rfl) _ (by positivity) (by positivity)
    apply mul_le_mul (by rfl) _ (by positivity) (by positivity)
    rw [abs_of_nonneg (by simp)]
    exact normPowerSeries_zpow_le_norm_sq_add_one n (m - 2) x hx
  · rw [Filter.eventually_iff_exists_mem]
    use {0}ᶜ
    constructor
    · rw [compl_mem_ae_iff, measure_singleton]
    intro x hx
    apply Filter.Tendsto.mul
    · exact tendsto_const_nhds
    simp [inner_smul_left, mul_assoc]
    apply Filter.Tendsto.mul
    · exact tendsto_const_nhds
    ring_nf
    apply Filter.Tendsto.mul
    · exact tendsto_const_nhds
    have h1 : Filter.Tendsto (fun x_1 => normPowerSeries x_1 x ^ ((m - 2 : ℤ) : ℝ))
      Filter.atTop (𝓝 (‖x‖ ^ ((m - 2 : ℤ) : ℝ))) := by
      refine Filter.Tendsto.rpow ?_ ?_ ?_
      · apply normPowerSeries_tendsto x hx
      · simp
      · left
        simpa using hx
    simp [-Int.cast_sub, Real.rpow_intCast] at h1
    convert h1 using 3
    · ring
    · ring

/-!

### A.11. Gradients of distributions based on logs

-/

lemma gradient_dist_normPowerSeries_log {d : ℕ} {n : ℕ} :
    distGrad (distOfFunction (fun x : Space d => Real.log (normPowerSeries n x)) (by fun_prop)) =
    distOfFunction (fun x : Space d => ((normPowerSeries n x) ^ (- 2 : ℤ)) • basis.repr x)
    (by fun_prop) := by
  ext1 η
  apply ext_inner_right ℝ
  intro y
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
        conv => enter [1, x]; rw [fderiv_log_normPowerSeries]
        fun_prop
      · fun_prop
      · exact η.differentiable
      · fun_prop
    _ = ∫ (x : Space d), η x * (⟪basis.repr.symm y, x⟫_ℝ * (normPowerSeries n x) ^ (- 2 : ℤ)) := by
      congr
      funext x
      rw [fderiv_log_normPowerSeries]
  congr
  funext x
  simp [inner_smul_left_eq_smul]
  left
  rw [real_inner_comm]
  rw [basis_repr_inner_eq]
  ring

/-!

#### A.11.1. The limits of gradients of distributions based on logs

-/

lemma gradient_dist_normPowerSeries_log_tendsTo_distGrad_norm {d : ℕ}
    (η : 𝓢(Space d.succ.succ, ℝ)) (y : EuclideanSpace ℝ (Fin d.succ.succ)) :
    Filter.Tendsto (fun n =>
    ⟪(distGrad (distOfFunction
    (fun x : Space d.succ.succ => Real.log (normPowerSeries n x)) (by fun_prop))) η, y⟫_ℝ)
    Filter.atTop
    (𝓝 (⟪distGrad (distOfFunction (fun x : Space d.succ.succ => Real.log ‖x‖)
    (IsDistBounded.log_norm)) η, y⟫_ℝ)) := by
  simp only [distGrad_inner_eq, Distribution.fderivD_apply, distOfFunction_apply]
  change Filter.Tendsto (fun n => -
    ∫ (x : Space d.succ.succ), fderiv ℝ η x (basis.repr.symm y) * Real.log (normPowerSeries n x))
    Filter.atTop (𝓝 (- ∫ (x : Space d.succ.succ), fderiv ℝ η x (basis.repr.symm y) * Real.log ‖x‖))
  apply Filter.Tendsto.neg
  apply MeasureTheory.tendsto_integral_of_dominated_convergence
    (bound := fun x => |fderiv ℝ η x (basis.repr.symm y)| * (‖x‖⁻¹ + (‖x‖ + 1)))
  · intro n
    apply IsDistBounded.aeStronglyMeasurable_fderiv_schwartzMap_smul (F := ℝ) ?_
    fun_prop
  · have h1 : Integrable (fun x => (fderiv ℝ (⇑η) x) (basis.repr.symm y) *
        (‖x‖⁻¹ + (‖x‖ + 1))) volume := by
      apply IsDistBounded.integrable_space_fderiv ?_
      apply IsDistBounded.add
      · exact IsDistBounded.inv
      · fun_prop
    rw [← integrable_norm_iff] at h1
    convert h1 using 1
    funext x
    simp only [Nat.succ_eq_add_one, norm_mul, Real.norm_eq_abs, mul_eq_mul_left_iff, abs_eq_zero]
    left
    rw [abs_of_nonneg (by positivity)]
    fun_prop
  · intro n
    rw [Filter.eventually_iff_exists_mem]
    use {0}ᶜ
    constructor
    · rw [compl_mem_ae_iff, measure_singleton]
    intro x hx
    simp at hx
    simp
    apply mul_le_mul (by rfl) _ (by positivity) (by positivity)
    exact normPowerSeries_log_le n x hx
  · rw [Filter.eventually_iff_exists_mem]
    use {0}ᶜ
    constructor
    · rw [compl_mem_ae_iff, measure_singleton]
    intro x hx
    apply Filter.Tendsto.mul
    · exact tendsto_const_nhds
    apply Filter.Tendsto.log
    · exact normPowerSeries_tendsto x hx
    · simpa using hx

lemma gradient_dist_normPowerSeries_log_tendsTo {d : ℕ}
    (η : 𝓢(Space d.succ.succ, ℝ)) (y : EuclideanSpace ℝ (Fin d.succ.succ)) :
    Filter.Tendsto (fun n =>
    ⟪(distGrad (distOfFunction (fun x : Space d.succ.succ => Real.log (normPowerSeries n x))
    (by fun_prop))) η, y⟫_ℝ)
    Filter.atTop
    (𝓝 (⟪distOfFunction (fun x : Space d.succ.succ => (‖x‖ ^ (- 2 : ℤ)) • basis.repr x) (by
    refine (IsDistBounded.zpow_smul_repr_self _ ?_)
    simp_all) η, y⟫_ℝ)) := by
  conv =>
    enter [1, n];
    rw [gradient_dist_normPowerSeries_log]
  simp only [Nat.succ_eq_add_one, Int.reduceNeg, distOfFunction_inner]
  have h1 (n : ℕ) (x : Space d.succ.succ) :
    η x * ⟪(normPowerSeries n x ^ (- 2 : ℤ)) • basis.repr x, y⟫_ℝ =
    η x * ((⟪basis.repr x, y⟫_ℝ * (normPowerSeries n x) ^ (- 2 : ℤ))) := by
    simp [inner_smul_left]
    ring_nf
    left
    trivial
  conv =>
    enter [1, n, 2, x];
    rw [h1 n x]
  apply MeasureTheory.tendsto_integral_of_dominated_convergence
    (bound := fun x => |η x| * |⟪basis.repr x, y⟫_ℝ| * ((‖x‖ + 1) ^ (- 2 : ℤ) + ‖x‖ ^ (- 2 : ℤ)))
  · intro n
    apply IsDistBounded.aeStronglyMeasurable_schwartzMap_smul (F := ℝ) ?_ η
    simp only [Nat.succ_eq_add_one, basis_repr_inner_eq]
    apply IsDistBounded.isDistBounded_mul_inner'
    fun_prop
  · have h1 : Integrable (fun x =>
        η x * ((⟪basis.repr x, y⟫_ℝ * ((‖x‖ + 1) ^ (- 2 : ℤ) + ‖x‖ ^ (- 2 : ℤ))))) volume := by
      apply IsDistBounded.integrable_space_mul ?_ η
      simp [mul_add]
      apply IsDistBounded.add
      · simp only [basis_repr_inner_eq]
        apply IsDistBounded.isDistBounded_mul_inner'
        refine IsDistBounded.norm_add_pos_nat_zpow (- 2) 1 ?_
        simp
      · simp only [basis_repr_inner_eq]
        convert IsDistBounded.mul_inner_pow_neg_two (basis.repr.symm y) using 1
        funext x
        simp [real_inner_comm]

    rw [← integrable_norm_iff] at h1
    convert h1 using 1
    funext x
    simp [mul_assoc]
    rw [abs_of_nonneg (by positivity)]
    simp only [true_or]
    fun_prop
  · intro n
    rw [Filter.eventually_iff_exists_mem]
    use {0}ᶜ
    constructor
    · rw [compl_mem_ae_iff, measure_singleton]
    intro x hx
    simp at hx
    simp [mul_assoc]
    apply mul_le_mul (by rfl) _ (by positivity) (by positivity)
    apply mul_le_mul (by rfl) _ (by positivity) (by positivity)
    rw [abs_of_nonneg (by simp)]
    exact normPowerSeries_zpow_le_norm_sq_add_one n (- 2 : ℤ) x hx
  · rw [Filter.eventually_iff_exists_mem]
    use {0}ᶜ
    constructor
    · rw [compl_mem_ae_iff, measure_singleton]
    intro x hx
    apply Filter.Tendsto.mul
    · exact tendsto_const_nhds
    simp [inner_smul_left, inner_smul_left]
    rw [mul_comm]
    apply Filter.Tendsto.mul
    · exact tendsto_const_nhds
    have h1 : Filter.Tendsto (fun x_1 => normPowerSeries x_1 x ^ ((- 2 : ℤ) : ℝ))
      Filter.atTop (𝓝 (‖x‖ ^ ((- 2 : ℤ) : ℝ))) := by
      refine Filter.Tendsto.rpow ?_ ?_ ?_
      · apply normPowerSeries_tendsto x hx
      · simp
      · left
        simpa using hx
    simpa using h1

/-!

## B. Distributions involving norms

-/

/-!

### B.1. The gradient of distributions based on powers

-/

lemma distGrad_distOfFunction_norm_zpow {d : ℕ} (m : ℤ) (hm : - (d.succ - 1 : ℕ) + 1 ≤ m) :
    distGrad (distOfFunction (fun x : Space d.succ => ‖x‖ ^ m)
      (IsDistBounded.pow m (by simp_all; omega)))
    = distOfFunction (fun x : Space d.succ => (m * ‖x‖ ^ (m - 2)) • basis.repr x) (by
      simp [← smul_smul]
      refine IsDistBounded.const_fun_smul ?_ ↑m
      apply IsDistBounded.zpow_smul_repr_self
      simp_all
      omega) := by
  ext1 η
  exact ext_inner_right ℝ fun y => tendsto_nhds_unique
    (gradient_dist_normPowerSeries_zpow_tendsTo_distGrad_norm m (by simp_all; omega) η y)
    (gradient_dist_normPowerSeries_zpow_tendsTo m hm η y)

/-!

### B.2. The gradient of distributions based on logs

-/

lemma distGrad_distOfFunction_log_norm {d : ℕ} :
    distGrad (distOfFunction (fun x : Space d.succ.succ => Real.log ‖x‖)
      (IsDistBounded.log_norm))
    = distOfFunction (fun x : Space d.succ.succ => (‖x‖ ^ (- 2 : ℤ)) • basis.repr x) (by
      refine (IsDistBounded.zpow_smul_repr_self _ ?_)
      simp_all) := by
  ext1 η
  exact ext_inner_right ℝ fun y => tendsto_nhds_unique
    (gradient_dist_normPowerSeries_log_tendsTo_distGrad_norm η y)
    (gradient_dist_normPowerSeries_log_tendsTo η y)

/-!

### B.3. Divergence equal dirac delta

We show that the divergence of `x ↦ ‖x‖ ^ (- d) • x` is equal to a multiple of the Dirac delta
at `0`.

The proof

-/
open Distribution

lemma distDiv_inv_pow_eq_dim {d : ℕ} :
    distDiv (distOfFunction (fun x : Space d.succ => ‖x‖ ^ (- d.succ : ℤ) • basis.repr x)
      (IsDistBounded.zpow_smul_repr_self (- d.succ : ℤ) (by omega))) =
      (d.succ * (volume (α := Space d.succ)).real (Metric.ball 0 1)) • diracDelta ℝ 0 := by
  ext η
  calc _
      _ = - ∫ x, ⟪‖x‖⁻¹ ^ d.succ • basis.repr x, Space.grad η x⟫_ℝ := by
        simp only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one, zpow_neg, distDiv_ofFunction,
          inv_pow]
        rfl
      _ = - ∫ x, ‖x‖⁻¹ ^ d * ⟪‖x‖⁻¹ • basis.repr x, Space.grad η x⟫_ℝ := by
        simp only [Nat.succ_eq_add_one, inv_pow, inner_smul_left, map_inv₀, conj_trivial, neg_inj]
        ring_nf
      _ = - ∫ x, ‖x‖⁻¹ ^ d * (_root_.deriv (fun a => η (a • ‖x‖⁻¹ • x)) ‖x‖) := by
        simp only [real_inner_comm,
          ← grad_inner_space_unit_vector _ _ (SchwartzMap.differentiable η)]
      _ = - ∫ r, ‖r.2.1‖⁻¹ ^ d * (_root_.deriv (fun a => η (a • r.1)) ‖r.2.1‖)
        ∂(volume (α := Space d.succ).toSphere.prod
        (Measure.volumeIoiPow (Module.finrank ℝ (Space d.succ) - 1))) := by
        rw [← MeasureTheory.MeasurePreserving.integral_comp (f := homeomorphUnitSphereProd _)
          (MeasureTheory.Measure.measurePreserving_homeomorphUnitSphereProd
          (volume (α := Space d.succ)))
          (Homeomorph.measurableEmbedding (homeomorphUnitSphereProd (Space d.succ)))]
        congr 1
        simp only [inv_pow, homeomorphUnitSphereProd_apply_snd_coe, norm_norm,
          homeomorphUnitSphereProd_apply_fst_coe]
        let f (x : Space d.succ) : ℝ :=
          (‖↑x‖ ^ d)⁻¹ * _root_.deriv (fun a => η (a • ‖↑x‖⁻¹ • ↑x)) ‖↑x‖
        conv_rhs =>
          enter [2, x]
          change f x.1
        rw [MeasureTheory.integral_subtype_comap (by simp), ← setIntegral_univ]
        change ∫ x in Set.univ, f x = ∫ (x : Space d.succ) in _, f x
        refine (setIntegral_congr_set ?_)
        rw [← MeasureTheory.ae_eq_set_compl]
        trans (∅ : Set (Space d.succ))
        · apply Filter.EventuallyEq.of_eq
          rw [← Set.compl_empty]
          exact compl_compl _
        · symm
          simp
      _ = - ∫ n, (∫ r, ‖r.1‖⁻¹ ^ d *
        (_root_.deriv (fun a => η (a • n)) ‖r.1‖)
        ∂((Measure.volumeIoiPow (Module.finrank ℝ (Space d.succ) - 1))))
        ∂(volume (α := Space d.succ).toSphere) := by
        rw [MeasureTheory.integral_prod]
        /- Integrable condition. -/
        convert integrable_isDistBounded_inner_grad_schwartzMap_spherical
          (IsDistBounded.inv_pow_smul_repr_self (d.succ) (by omega)) η
        rename_i r
        simp only [Nat.succ_eq_add_one, Real.norm_eq_abs, inv_pow, Function.comp_apply,
          homeomorphUnitSphereProd_symm_apply_coe]
        let x : Space d.succ := r.2.1 • r.1.1
        have hr := r.2.2
        simp [-Subtype.coe_prop] at hr
        have hr2 : r.2.1 ≠ 0 := by exact Ne.symm (ne_of_lt hr)
        rw [abs_of_nonneg (le_of_lt hr)]
        trans (r.2.1 ^ d)⁻¹ * _root_.deriv (fun a => η (a • ‖↑x‖⁻¹ • ↑x)) ‖x‖
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
        rw [← grad_inner_space_unit_vector]
        rw [real_inner_comm]
        simp [inner_smul_left, x, norm_smul, abs_of_nonneg (le_of_lt hr)]
        field_simp
        ring
        exact SchwartzMap.differentiable η
      _ = - ∫ n, (∫ (r : Set.Ioi (0 : ℝ)),
        (_root_.deriv (fun a => η (a • n)) r.1) ∂(.comap Subtype.val volume))
        ∂(volume (α := Space d.succ).toSphere) := by
        congr
        funext n
        simp [Measure.volumeIoiPow]
        erw [integral_withDensity_eq_integral_smul]
        congr
        funext r
        have hr := r.2
        simp [-Subtype.coe_prop] at hr
        trans ((r.1 ^ d).toNNReal : ℝ) • ((r.1 ^ d)⁻¹ * _root_.deriv (fun a => η (a • ↑n)) |r.1|)
        · rw [NNReal.smul_def]
          simp only [Real.coe_toNNReal', smul_eq_mul, Nat.succ_eq_add_one, mul_eq_mul_left_iff,
            mul_eq_mul_right_iff, inv_inj, sup_eq_right]
          rw [abs_of_nonneg (le_of_lt hr)]
          simp
        trans ((r.1 ^ d) : ℝ) • ((r.1 ^ d)⁻¹ * _root_.deriv (fun a => η (a • ↑n)) |r.1|)
        · congr
          rw [Real.coe_toNNReal']
          rw [max_eq_left]
          apply pow_nonneg
          grind
        have h1 : r.1 ≠ 0 := by exact ne_of_gt r.2
        simp only [smul_eq_mul]
        field_simp
        congr
        rw [abs_of_nonneg (le_of_lt hr)]
        fun_prop
      _ = - ∫ n, (-η 0) ∂(volume (α := Space d.succ).toSphere) := by
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
              simp [fderiv_smul_const, iteratedFDeriv_succ_eq_comp_right,
                ContinuousLinearMap.norm_id]
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
        rw [MeasureTheory.integral_subtype_comap (by simp)]
        rw [MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto (f := fun a => η (a • n)) (m := 0)]
        · simp
        · refine ContinuousAt.continuousWithinAt ?_
          fun_prop
        · intro x hx
          refine DifferentiableAt.hasDerivAt ?_
          have := η.differentiable
          fun_prop
        · exact (integrable ((derivCLM ℝ ℝ) (η' n))).integrableOn
        · exact Filter.Tendsto.mono_left (η' n).toZeroAtInfty.zero_at_infty' atTop_le_cocompact
      _ = η 0 * (d.succ * (volume (α := Space d.succ)).real (Metric.ball 0 1)) := by
        simp only [Nat.succ_eq_add_one, integral_const, Measure.toSphere_real_apply_univ,
          finrank_eq_dim, Nat.cast_add, Nat.cast_one, smul_eq_mul, mul_neg, neg_neg]
        ring
  simp only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one, ContinuousLinearMap.coe_smul',
    Pi.smul_apply, diracDelta_apply, smul_eq_mul]
  ring

end Space
