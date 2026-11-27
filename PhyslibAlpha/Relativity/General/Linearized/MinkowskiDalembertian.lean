/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import PhyslibAlpha.Relativity.General.Linearized.Laplacian3
import Mathlib.Tactic.Ring

/-!

# Minkowski d'Alembertian wave operator

The flat-space d'Alembertian `□_η f = η^{μν} ∂_μ ∂_ν f` on four-dimensional Minkowski spacetime.

## i. Overview

In `(-, +, +, +)` signature, the flat-space wave operator is defined by
`minkowskiDalembertian f x = ∑ μ, η_{μμ} ∂_μ ∂_μ f(x) = -∂_0² f + ∂_1² f + ∂_2² f + ∂_3² f`.
It governs both gravitational radiation in Lorenz gauge and scalar wave equations on Minkowski
spacetime (such as Nordström gravity), and reduces on static fields (`∂_0 Φ = 0`) to `laplacian3`.

## ii. Key results

- `minkowskiDalembertian` : Minkowski d'Alembertian wave operator `□_η`.
- `minkowskiDalembertian_zero`, `minkowskiDalembertian_const_mul`, `minkowskiDalembertian_neg`,
  `minkowskiDalembertian_add` : vanishing on zero and linearity under scalar multiplication,
  negation, and addition.
- `minkowskiDalembertian_eq_laplacian3_of_static` : static reduction `□_η Φ = ∇² Φ`.

## iii. Table of contents

- A. The Minkowski d'Alembertian `□_η`

## iv. References

* R. M. Wald, *General Relativity* (1984), Ch. 4 (Sec. 4.4). [ref: wald_1984_general_relativity]
* C. W. Misner, K. S. Thorne, and J. A. Wheeler, *Gravitation* (1973), Ch. 18 & Ch. 35.
  [ref: mtw_1973_gravitation]
* S. M. Carroll, *Lecture Notes on General Relativity* (1997), Ch. 6
  (https://arxiv.org/pdf/gr-qc/9712019#page=150). [ref: Carroll1997]
-/

@[expose] public section

namespace GeneralRelativity

namespace Linearized

open CoordinateCurvature

/-!

## A. The Minkowski d'Alembertian `□_η`

The flat-space hyperbolic wave operator `-∂_t² + ∇²` obtained by contracting second coordinate
derivatives with the Minkowski metric `η^{μν}`.

-/

/-- Minkowski d'Alembertian (wave operator) `□f = η^{μν} ∂_μ ∂_ν f = -∂_t² f + ∇² f`. -/
noncomputable def minkowskiDalembertian (f : (Fin 4 → ℝ) → ℝ) (x : Fin 4 → ℝ) : ℝ :=
  ∑ μ : Fin 4, minkowskiMetric4 μ μ * coordDeriv μ (coordDeriv μ f) x

/-- Applying `minkowskiDalembertian` to the identically zero scalar function yields `0`. -/
lemma minkowskiDalembertian_zero (x : Fin 4 → ℝ) :
    minkowskiDalembertian (fun _ : Fin 4 → ℝ => (0 : ℝ)) x = 0 := by
  have hpd : ∀ μ : Fin 4, coordDeriv μ (fun _ : Fin 4 → ℝ => (0 : ℝ)) = fun _ => 0 :=
    fun μ => funext fun y => coordDeriv_const μ 0 y
  simp only [minkowskiDalembertian, hpd, coordDeriv_const, mul_zero, Finset.sum_const_zero]

/-- Scaling linearity of the Minkowski d'Alembertian: `□_η (c f) = c □_η f`. -/
lemma minkowskiDalembertian_const_mul (c : ℝ) (f : (Fin 4 → ℝ) → ℝ) (x : Fin 4 → ℝ) :
    minkowskiDalembertian (fun y => c * f y) x = c * minkowskiDalembertian f x := by
  have hev : ∀ μ : Fin 4,
      coordDeriv μ (fun y => c * f y) = fun y => c * coordDeriv μ f y :=
    fun μ => funext fun y => coordDeriv_const_mul μ c y
  simp only [minkowskiDalembertian, hev, coordDeriv_const_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ _ => by ring

/-- Sign linearity of the Minkowski d'Alembertian: `□_η (-f) = -□_η f`. -/
lemma minkowskiDalembertian_neg (f : (Fin 4 → ℝ) → ℝ) (x : Fin 4 → ℝ) :
    minkowskiDalembertian (fun y => -f y) x = -minkowskiDalembertian f x := by
  have hfun : (fun y => -f y) = fun y => (-1 : ℝ) * f y := funext fun y => by ring
  rw [hfun, minkowskiDalembertian_const_mul]
  ring

/-- Additivity of the Minkowski d'Alembertian on `C²` scalar fields `f` and `g` at `x`. -/
lemma minkowskiDalembertian_add (f g : (Fin 4 → ℝ) → ℝ) (x : Fin 4 → ℝ)
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) :
    minkowskiDalembertian (fun y => f y + g y) x =
      minkowskiDalembertian f x + minkowskiDalembertian g x := by
  have hf_nhds : ∀ᶠ y in nhds x, ContDiffAt ℝ 2 f y := hf.eventually (by simp)
  have hg_nhds : ∀ᶠ y in nhds x, ContDiffAt ℝ 2 g y := hg.eventually (by simp)
  have hterm : ∀ μ : Fin 4,
      coordDeriv μ (coordDeriv μ fun y => f y + g y) x =
        coordDeriv μ (coordDeriv μ f) x + coordDeriv μ (coordDeriv μ g) x := by
    intro μ
    have hcongr : coordDeriv μ (fun y => f y + g y) =ᶠ[nhds x]
        fun y => coordDeriv μ f y + coordDeriv μ g y := by
      filter_upwards [hf_nhds, hg_nhds] with y hyf hyg
      exact coordDeriv_add μ y (slice_differentiableAt μ (hyf.differentiableAt (by norm_num)))
        (slice_differentiableAt μ (hyg.differentiableAt (by norm_num)))
    rw [coordDeriv_congr_nhds μ x hcongr,
      coordDeriv_add μ x (slice_differentiableAt μ (coordDeriv_differentiableAt μ hf))
        (slice_differentiableAt μ (coordDeriv_differentiableAt μ hg))]
  simp only [minkowskiDalembertian, hterm, mul_add, Finset.sum_add_distrib]

/-- For a static scalar field (`∂_0 Φ = 0`), the Minkowski d'Alembertian reduces to `laplacian3`. -/
lemma minkowskiDalembertian_eq_laplacian3_of_static (Φ : (Fin 4 → ℝ) → ℝ) (x : Fin 4 → ℝ)
    (hstat : ∀ y, coordDeriv 0 Φ y = 0) :
    minkowskiDalembertian Φ x = laplacian3 Φ x := by
  have h0fun : coordDeriv 0 Φ = fun _ => 0 := funext hstat
  simp only [minkowskiDalembertian, laplacian3, Fin.sum_univ_four, minkowskiMetric4_apply,
    h0fun, coordDeriv_const]
  norm_num

end Linearized

end GeneralRelativity
