/-
Copyright (c) 2026 Daniel Leonforte. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Leonforte
-/
module

public import PhyslibAlpha.QuantumMechanics.Hydrogen.PolyBounded
public import Mathlib.Analysis.Calculus.ContDiff.Polynomial

/-!
# Green's identity and regularised radial functions

## i. Overview

For a `C²` function `u` on `Space d` such that `u`, `∂ᵢu` and `∂ᵢ∂ᵢu` are polynomially bounded and
a Schwartz map `f`, Green's identity `∫ u Δf = ∫ (Δu) f` holds (two integrations by parts).
Functions of the form `R(‖y‖) Q(y)` are in general not smooth at the origin; replacing `‖y‖` by
the regularised radius `ρ_ε = √(‖y‖² + ε²)` makes them smooth for `ε ≠ 0`. This module provides
the derivatives of `G(‖y‖²) Q(y)` and the polynomial bounds needed to apply Green's identity to the
regularised functions, uniformly in `|ε| ≤ 1` when `R` is a polynomial times `e^(-κr)`.

## ii. Key results

- `integral_ofReal_mul_sum_deriv_deriv` : Green's identity `∫ u Σᵢ∂ᵢ∂ᵢf = ∫ (Σᵢ∂ᵢ∂ᵢu) f`.
- `deriv_radial_mul`, `deriv_deriv_radial_mul` : first and second coordinate derivatives of
  `G(‖y‖²) Q(y)` at every point.
- `regG`, `hasDerivAt_regG`, `hasDerivAt_regG'` : the regularised profile `s ↦ f(√(s + ε²))` and
  its derivatives.
- `isPolyBounded_regG`, `isPolyBounded_regG'`, `isPolyBounded_regG''`,
  `exists_abs_poly_exp_regRadius_le` : polynomial bounds, uniform in `|ε| ≤ 1`.

## iii. Table of contents

- A. Green's identity for smooth functions
- B. Derivatives of radial functions
- C. Regularised radial profiles

## iv. References

- None.
-/

@[expose] public section

noncomputable section

namespace PhyslibAlpha.Hydrogen

open MeasureTheory Space
open scoped SchwartzMap LineDeriv

/-!

## A. Green's identity for smooth functions

-/

/-- The derivative of a real function, viewed as a complex function. -/
lemma deriv_ofReal {d : ℕ} {u : Space d → ℝ} (hu : Differentiable ℝ u) (i : Fin d) (y : Space d) :
    ∂[i] (fun y => (u y : ℂ)) y = ((∂[i] u y : ℝ) : ℂ) := by
  rw [Space.deriv_eq, Space.deriv_eq,
    show (fun y => (u y : ℂ)) = ⇑Complex.ofRealCLM ∘ u from rfl,
    (Complex.ofRealCLM.hasFDerivAt.comp y (hu y).hasFDerivAt).fderiv]
  rfl

/-- The coordinate derivative of a Schwartz map, as a Schwartz map. -/
lemma deriv_schwartz {d : ℕ} (f : 𝓢(Space d, ℂ)) (i : Fin d) :
    ∂[i] ⇑f = ⇑(∂_{Space.basis i} f : 𝓢(Space d, ℂ)) := by
  funext y
  rw [Space.deriv_eq, SchwartzMap.lineDerivOp_apply_eq_fderiv]

/-- **Green's identity for smooth functions.** If `u` is `C²` and `u`, `∂ᵢu`, `∂ᵢ∂ᵢu` are
polynomially bounded, then `∫ u Σᵢ ∂ᵢ∂ᵢ f = ∫ (Σᵢ ∂ᵢ∂ᵢ u) f` for every Schwartz map `f`. -/
lemma integral_ofReal_mul_sum_deriv_deriv {d : ℕ} {u : Space d → ℝ} (hu : ContDiff ℝ 2 u)
    (hb0 : IsPolyBounded u) (hb1 : ∀ i, IsPolyBounded (∂[i] u))
    (hb2 : ∀ i, IsPolyBounded (∂[i] (∂[i] u))) (f : 𝓢(Space d, ℂ)) :
    ∫ y, (u y : ℂ) * ∑ i, ∂[i] (∂[i] ⇑f) y =
      ∫ y, ((∑ i, ∂[i] (∂[i] u) y : ℝ) : ℂ) * f y := by
  have hu1 : Differentiable ℝ u := hu.differentiable (by norm_num)
  have hdu : ∀ i, Differentiable ℝ (∂[i] u) := fun i => Space.deriv_differentiable hu i
  have hm0 : AEStronglyMeasurable u := hu.continuous.aestronglyMeasurable
  have hm1 : ∀ i, AEStronglyMeasurable (∂[i] u) := fun i => (hdu i).continuous.aestronglyMeasurable
  have hm2 : ∀ i, AEStronglyMeasurable (∂[i] (∂[i] u)) := fun i =>
    (measurable_fderiv_apply_const ℝ (∂[i] u) (Space.basis i)).aestronglyMeasurable
  -- one coordinate at a time
  have key : ∀ i, ∫ y, (u y : ℂ) * ∂[i] (∂[i] ⇑f) y =
      ∫ y, ((∂[i] (∂[i] u) y : ℝ) : ℂ) * f y := by
    intro i
    have h1 : ∫ y, (u y : ℂ) * ∂[i] (∂[i] ⇑f) y =
        -∫ y, ((∂[i] u y : ℝ) : ℂ) * ∂[i] ⇑f y := by
      rw [deriv_schwartz f i, deriv_schwartz (∂_{Space.basis i} f : 𝓢(Space d, ℂ)) i]
      have := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
        (f := fun y => (u y : ℂ)) (g := ⇑(∂_{Space.basis i} f : 𝓢(Space d, ℂ)))
        (v := Space.basis i)
        (by simpa [← Space.deriv_eq, deriv_ofReal hu1] using
          (hb1 i).integrable_ofReal_mul_schwartz (hm1 i) (∂_{Space.basis i} f : 𝓢(Space d, ℂ)))
        (by simpa [← SchwartzMap.lineDerivOp_apply_eq_fderiv] using
          hb0.integrable_ofReal_mul_schwartz hm0
              ((∂_{Space.basis i} (∂_{Space.basis i} f) : 𝓢(Space d, ℂ))))
        (hb0.integrable_ofReal_mul_schwartz hm0 (∂_{Space.basis i} f : 𝓢(Space d, ℂ)))
        (fun y _ => (Complex.ofRealCLM.differentiable.comp hu1) y)
        (fun y _ => (∂_{Space.basis i} f : 𝓢(Space d, ℂ)).differentiableAt)
      simpa [← Space.deriv_eq, deriv_ofReal hu1, ← SchwartzMap.lineDerivOp_apply_eq_fderiv]
        using this
    have h2 : ∫ y, ((∂[i] u y : ℝ) : ℂ) * ∂[i] ⇑f y = -∫ y, ((∂[i] (∂[i] u) y : ℝ) : ℂ) * f y := by
      rw [deriv_schwartz f i]
      have := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
        (f := fun y => ((∂[i] u y : ℝ) : ℂ)) (g := ⇑f) (v := Space.basis i)
        (by simpa [← Space.deriv_eq, deriv_ofReal (hdu i)] using
          (hb2 i).integrable_ofReal_mul_schwartz (hm2 i) f)
        (by simpa [← SchwartzMap.lineDerivOp_apply_eq_fderiv] using
          (hb1 i).integrable_ofReal_mul_schwartz (hm1 i) (∂_{Space.basis i} f : 𝓢(Space d, ℂ)))
        ((hb1 i).integrable_ofReal_mul_schwartz (hm1 i) f)
        (fun y _ => (Complex.ofRealCLM.differentiable.comp (hdu i)) y)
        (fun y _ => f.differentiableAt)
      simpa [← Space.deriv_eq, deriv_ofReal (hdu i), ← SchwartzMap.lineDerivOp_apply_eq_fderiv]
        using this
    rw [h1, h2, neg_neg]
  -- sum over the coordinates
  have hintL : ∀ i ∈ Finset.univ, Integrable (fun y => (u y : ℂ) * ∂[i] (∂[i] ⇑f) y) := by
    intro i _
    rw [deriv_schwartz f i, deriv_schwartz (∂_{Space.basis i} f) i]
    exact hb0.integrable_ofReal_mul_schwartz hm0 _
  have hintR : ∀ i ∈ Finset.univ, Integrable (fun y => ((∂[i] (∂[i] u) y : ℝ) : ℂ) * f y) :=
    fun i _ => (hb2 i).integrable_ofReal_mul_schwartz (hm2 i) f
  simp only [Finset.mul_sum, Complex.ofReal_sum, Finset.sum_mul]
  rw [integral_finsetSum _ hintL, integral_finsetSum _ hintR]
  exact Finset.sum_congr rfl fun i _ => key i

/-!

## B. Derivatives of radial functions

-/

/-- `∂ᵢ (G(‖y‖²) Q) = G ∂ᵢQ + Q G' 2yᵢ` at every point, if `G` is differentiable on `[0, ∞)`. -/
lemma deriv_radial_mul {d : ℕ} {G G' : ℝ → ℝ} (hG : ∀ s, 0 ≤ s → HasDerivAt G (G' s) s)
    {Q : Space d → ℝ} (hQ : Differentiable ℝ Q) (i : Fin d) :
    ∂[i] (fun y => G (‖y‖ ^ 2) * Q y) =
      fun y => G (‖y‖ ^ 2) * ∂[i] Q y + Q y * (G' (‖y‖ ^ 2) * (2 * y i)) := by
  funext y
  rw [deriv_mul_apply (differentiableAt_comp_normSq (hG _ (sq_nonneg _))) (hQ y),
    deriv_comp_normSq (hG _ (sq_nonneg _))]

/-- `∂ᵢ∂ᵢ (G(‖y‖²) Q) = G ∂ᵢ∂ᵢQ + 4 G' yᵢ ∂ᵢQ + (2 G' + 4 yᵢ² G'') Q` at every point. -/
lemma deriv_deriv_radial_mul {d : ℕ} {G G' G'' : ℝ → ℝ}
    (hG : ∀ s, 0 ≤ s → HasDerivAt G (G' s) s) (hG' : ∀ s, 0 ≤ s → HasDerivAt G' (G'' s) s)
    {Q : Space d → ℝ} (hQ : ContDiff ℝ 2 Q) (i : Fin d) (x : Space d) :
    ∂[i] (∂[i] (fun y => G (‖y‖ ^ 2) * Q y)) x = G (‖x‖ ^ 2) * ∂[i] (∂[i] Q) x +
      4 * G' (‖x‖ ^ 2) * (x i * ∂[i] Q x) +
        (2 * G' (‖x‖ ^ 2) + 4 * x i ^ 2 * G'' (‖x‖ ^ 2)) * Q x := by
  have hQd : Differentiable ℝ Q := hQ.differentiable (by norm_num)
  rw [deriv_radial_mul hG hQd i]
  have hGd := differentiableAt_comp_normSq (x := x) (hG _ (sq_nonneg _))
  have hG'd := differentiableAt_comp_normSq (x := x) (hG' _ (sq_nonneg _))
  have hxi : DifferentiableAt ℝ (fun y : Space d => 2 * y i) x :=
    ((eval_differentiable i) x).const_mul 2
  have hdQ : Differentiable ℝ (∂[i] Q) := Space.deriv_differentiable hQ i
  rw [deriv_add_apply (A := fun y => G (‖y‖ ^ 2) * ∂[i] Q y)
      (B := fun y => Q y * (G' (‖y‖ ^ 2) * (2 * y i))) (hGd.mul (hdQ x))
      ((hQd x).mul (hG'd.mul hxi)),
    deriv_mul_apply hGd (hdQ x),
    deriv_mul_apply (B := fun y => G' (‖y‖ ^ 2) * (2 * y i)) (hQd x) (hG'd.mul hxi),
    deriv_mul_apply hG'd hxi,
    deriv_comp_normSq (hG _ (sq_nonneg _)), deriv_comp_normSq (hG' _ (sq_nonneg _))]
  have hc : ∂[i] (fun y : Space d => 2 * y i) x = 2 := by
    rw [Space.deriv_eq, fderiv_const_mul ((eval_differentiable i) x),
      _root_.smul_apply, ← Space.deriv_eq, deriv_component_same]
    simp
  rw [hc]
  ring

/-!

## C. Regularised radial profiles

-/

/-- The regularised radial profile `s ↦ f(√(s + ε²))`, smooth also at `s = 0`. -/
def regG (f : ℝ → ℝ) (ε s : ℝ) : ℝ := f (Real.sqrt (s + ε ^ 2))

/-- The derivative of `regG f ε`. -/
def regG' (f' : ℝ → ℝ) (ε s : ℝ) : ℝ :=
  f' (Real.sqrt (s + ε ^ 2)) / (2 * Real.sqrt (s + ε ^ 2))

/-- The second derivative of `regG f ε`. -/
def regG'' (f' f'' : ℝ → ℝ) (ε s : ℝ) : ℝ :=
  (f'' (Real.sqrt (s + ε ^ 2)) - f' (Real.sqrt (s + ε ^ 2)) / Real.sqrt (s + ε ^ 2)) /
    (4 * (s + ε ^ 2))

lemma hasDerivAt_regG {f f' : ℝ → ℝ} (hf : ∀ r, 0 < r → HasDerivAt f (f' r) r) {ε s : ℝ}
    (hs : 0 < s + ε ^ 2) : HasDerivAt (regG f ε) (regG' f' ε s) s := by
  have h := (hasDerivAt_comp_sqrt hf (s := s + ε ^ 2) hs).comp s
    ((hasDerivAt_id s).add_const (ε ^ 2))
  change HasDerivAt (fun s => f (Real.sqrt (s + ε ^ 2))) (regG' f' ε s) s
  simpa [regG', Function.comp_def] using h

lemma hasDerivAt_regG' {f' f'' : ℝ → ℝ} (hf : ∀ r, 0 < r → HasDerivAt f' (f'' r) r) {ε s : ℝ}
    (hs : 0 < s + ε ^ 2) : HasDerivAt (regG' f' ε) (regG'' f' f'' ε s) s := by
  have h := (hasDerivAt_comp_sqrt' hf (s := s + ε ^ 2) hs).comp s
    ((hasDerivAt_id s).add_const (ε ^ 2))
  change HasDerivAt (fun s => f' (Real.sqrt (s + ε ^ 2)) / (2 * Real.sqrt (s + ε ^ 2)))
    (regG'' f' f'' ε s) s
  simpa [regG'', Function.comp_def] using h

/-- The regularised radius `√(‖y‖² + ε²)` is at least `|ε|`. -/
lemma abs_le_regRadius {d : ℕ} (ε : ℝ) (y : Space d) : |ε| ≤ Real.sqrt (‖y‖ ^ 2 + ε ^ 2) :=
  Real.abs_le_sqrt (by nlinarith [sq_nonneg ‖y‖])

lemma isPolyBounded_regRadius {d : ℕ} (ε : ℝ) :
    IsPolyBounded (fun y : Space d => Real.sqrt (‖y‖ ^ 2 + ε ^ 2)) := by
  refine ⟨|ε| + 1, 1, by positivity, fun y => ?_⟩
  have h1 : Real.sqrt (‖y‖ ^ 2 + ε ^ 2) ≤ ‖y‖ + |ε| := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith [norm_nonneg y, abs_nonneg ε, sq_abs ε]
  rw [abs_of_nonneg (Real.sqrt_nonneg _), pow_one]
  nlinarith [norm_nonneg y, abs_nonneg ε]

/-- A polynomial in the regularised radius times `e^(-κρ)`, `κ ≥ 0`, is polynomially bounded. -/
lemma isPolyBounded_poly_exp_regRadius {d : ℕ} (p : Polynomial ℝ) {κ : ℝ} (hκ : 0 ≤ κ)
    (ε : ℝ) : IsPolyBounded (fun y : Space d =>
      p.eval (Real.sqrt (‖y‖ ^ 2 + ε ^ 2)) * Real.exp (-(κ * Real.sqrt (‖y‖ ^ 2 + ε ^ 2)))) := by
  refine ((isPolyBounded_regRadius ε).polynomial_eval p).mono zero_le_one fun y => ?_
  rw [abs_mul, one_mul, abs_of_pos (Real.exp_pos _)]
  exact mul_le_of_le_one_right (abs_nonneg _)
    (Real.exp_le_one_iff.mpr (by have := Real.sqrt_nonneg (‖y‖ ^ 2 + ε ^ 2); nlinarith))

lemma isPolyBounded_inv_regRadius {d : ℕ} {ε : ℝ} (hε : ε ≠ 0) :
    IsPolyBounded (fun y : Space d => (Real.sqrt (‖y‖ ^ 2 + ε ^ 2))⁻¹) :=
  IsPolyBounded.of_abs_le_const (c := |ε|⁻¹) fun y => by
    rw [abs_inv, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact inv_anti₀ (abs_pos.mpr hε) (abs_le_regRadius ε y)

/-- The profiles `G_ε`, `G_ε'`, `G_ε''` of `f(r) = p(r) e^(-κr)` on `‖y‖²` are polynomially
bounded for fixed `ε ≠ 0`. -/
lemma isPolyBounded_regG {d : ℕ} (p : Polynomial ℝ) {κ : ℝ} (hκ : 0 ≤ κ) (ε : ℝ) :
    IsPolyBounded (fun y : Space d =>
      regG (fun r => p.eval r * Real.exp (-(κ * r))) ε (‖y‖ ^ 2)) :=
  isPolyBounded_poly_exp_regRadius p hκ ε

lemma isPolyBounded_regG' {d : ℕ} (q : Polynomial ℝ) {κ : ℝ} (hκ : 0 ≤ κ) {ε : ℝ}
    (hε : ε ≠ 0) :
    IsPolyBounded (fun y : Space d =>
      regG' (fun r => q.eval r * Real.exp (-(κ * r))) ε (‖y‖ ^ 2)) := by
  have h := ((isPolyBounded_poly_exp_regRadius (d := d) q hκ ε).mul
    (isPolyBounded_inv_regRadius (d := d) hε)).mul (IsPolyBounded.const (2 : ℝ)⁻¹)
  refine h.mono zero_le_one fun y => le_of_eq ?_
  simp only [regG', one_mul]
  congr 1
  field_simp

lemma isPolyBounded_regG'' {d : ℕ} (q q' : Polynomial ℝ) {κ : ℝ} (hκ : 0 ≤ κ) {ε : ℝ}
    (hε : ε ≠ 0) :
    IsPolyBounded (fun y : Space d =>
      regG'' (fun r => q.eval r * Real.exp (-(κ * r))) (fun r => q'.eval r * Real.exp (-(κ * r)))
        ε (‖y‖ ^ 2)) := by
  have hρ := isPolyBounded_inv_regRadius (d := d) hε
  have h := ((isPolyBounded_poly_exp_regRadius (d := d) q' hκ ε).add
    ((isPolyBounded_poly_exp_regRadius (d := d) q hκ ε).mul hρ).neg).mul
      ((hρ.mul hρ).mul (IsPolyBounded.const (4 : ℝ)⁻¹))
  refine h.mono zero_le_one fun y => le_of_eq ?_
  have hpos : 0 < Real.sqrt (‖y‖ ^ 2 + ε ^ 2) :=
    lt_of_lt_of_le (abs_pos.mpr hε) (abs_le_regRadius ε y)
  have hsq : ‖y‖ ^ 2 + ε ^ 2 = Real.sqrt (‖y‖ ^ 2 + ε ^ 2) ^ 2 :=
    (Real.sq_sqrt (by positivity)).symm
  simp only [regG'', one_mul]
  set ρ := Real.sqrt (‖y‖ ^ 2 + ε ^ 2)
  congr 1
  rw [hsq]
  field_simp
  ring

/-- A bound for `p(ρ) e^(-κρ)`, `ρ = √(‖y‖² + ε²)`, uniform in `|ε| ≤ 1`. -/
lemma exists_abs_poly_exp_regRadius_le {d : ℕ} (p : Polynomial ℝ) {κ : ℝ} (hκ : 0 ≤ κ) :
    ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧ ∀ ε : ℝ, |ε| ≤ 1 → ∀ y : Space d,
      |p.eval (Real.sqrt (‖y‖ ^ 2 + ε ^ 2)) * Real.exp (-(κ * Real.sqrt (‖y‖ ^ 2 + ε ^ 2)))| ≤
        C * (1 + ‖y‖) ^ k := by
  obtain ⟨C, k, hC, hb⟩ := Polynomial.exists_abs_eval_le p
  refine ⟨C * 2 ^ k, k, by positivity, fun ε hε y => ?_⟩
  set ρ := Real.sqrt (‖y‖ ^ 2 + ε ^ 2)
  have hρ0 : 0 ≤ ρ := Real.sqrt_nonneg _
  have hρ : ρ ≤ ‖y‖ + 1 := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith [norm_nonneg y, sq_abs ε, abs_nonneg ε]
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  have he : Real.exp (-(κ * ρ)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  calc |p.eval ρ| * Real.exp (-(κ * ρ)) ≤ |p.eval ρ| := mul_le_of_le_one_right (abs_nonneg _) he
    _ ≤ C * (1 + |ρ|) ^ k := hb ρ
    _ ≤ C * (2 * (1 + ‖y‖)) ^ k := by
      gcongr
      rw [abs_of_nonneg hρ0]
      linarith [norm_nonneg y]
    _ = C * 2 ^ k * (1 + ‖y‖) ^ k := by rw [mul_pow]; ring

end PhyslibAlpha.Hydrogen
