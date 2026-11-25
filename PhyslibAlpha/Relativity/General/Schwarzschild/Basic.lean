/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import PhyslibAlpha.Relativity.General.Schwarzschild.ElectricWeyl
public import PhyslibAlpha.Relativity.General.Schwarzschild.IncompressibleSphere
public import PhyslibAlpha.Relativity.Metrics.StaticSphericalMetric
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!

# Schwarzschild curvature from the metric components

Derivation of the Christoffel symbols, all six independent Riemann curvature components, and the
orthonormal-frame Weyl electric eigenvalues directly from the Schwarzschild line element.

## i. Overview

Starting from `g = diag(-f, f⁻¹, r², r² sin²θ)` with lapse `f = 1 - 2M/r`, this module computes
the coordinate derivatives of the metric components, assembles the non-vanishing Christoffel
symbols (`Γ^t_{tr}`, `Γ^r_{rr}`, `Γ^r_{θθ}`, `Γ^r_{φφ}`, `Γ^θ_{φφ}`, `Γ^φ_{θφ}`), and
evaluates all six independent Riemann components `R^t_{rtr}`, `R^t_{θtθ}`, `R^t_{φtφ}`,
`R^r_{θrθ}`, `R^r_{φrφ}`, `R^θ_{φθφ}`, along with their frame electric eigenvalues `(-2k, k, k)`
at `k = M / r³`. Note that this module uses signature `(-, +, +, +)` (`g_tt = -f`), whereas
`IncompressibleSphere.gttOut` stores the positive lapse factor `f = 1 - r_s / r` directly.

## ii. Key results

- `SchwarzschildSpacetime`, `SchwarzschildSpacetime.lapse`, `SchwarzschildSpacetime.metric`,
  `schwarzschildMetric`, `schwarzschildF` : Schwarzschild spacetime structure, coordinate metric,
  and lapse function `1 - 2M / r`.
- `schwarzschildF_of_incompressibleSphere`, `schwarzschildMetric_tt_of_incompressibleSphere`,
  `schwarzschildMetric_rr_of_incompressibleSphere` : exterior matching with `IncompressibleSphere`.
- `gammaTtr_from_metric`, `gammaRrr_from_metric`, `gammaRthth_from_metric`,
  `gammaRphiphi_from_metric`, `gammaThetaphiphi_from_metric`, `gammaPhiphitheta_from_metric` :
  non-vanishing Christoffel symbols derived from the metric.
- `riemann_t_rtr_from_metric`, `riemann_t_thetatheta_from_metric`,
  `riemann_t_phitphi_from_metric`, `riemann_r_thetar_from_metric`,
  `riemann_r_phirphi_from_metric`, `riemann_theta_phitheta_from_metric` : all six independent
  Riemann components derived from the metric.
- `electricPart_from_metric`, `riemann_components_from_metric` : bundled frame electric part
  and curvature components from the metric.

## iii. Table of contents

- A. The Schwarzschild lapse and radial Christoffel symbols
- B. Electric Riemann components and tidal eigenvalues
- C. Remaining independent Riemann components
- D. Assembled curvature and electric part statements

## iv. References

* R. M. Wald, *General Relativity* (1984). [ref: wald_1984_general_relativity]
* C. W. Misner, K. S. Thorne, and J. A. Wheeler, *Gravitation* (1973). [ref: mtw_1973_gravitation]

-/

@[expose] public section

namespace GeneralRelativity

namespace Schwarzschild

/-!

## A. The Schwarzschild lapse and radial Christoffel symbols

From the Schwarzschild lapse `f = 1 - 2M/r` and diagonal inverse metric `diag(-f⁻¹, f, r⁻²,
r⁻² sin⁻²θ)`, differentiating the radial metric components determines the mixed Christoffel symbols
`Γ^t_{tr}` and `Γ^r_{rr}`.

-/

/-- Exterior Schwarzschild black hole spacetime parameterized by geometric mass `M`. -/
structure SchwarzschildSpacetime where
  /-- Geometric mass parameter `M` (`G = c = 1`). -/
  M : ℝ

/-- The Schwarzschild metric lapse function `f = 1 - 2M / r`. -/
noncomputable def schwarzschildF (M r : ℝ) : ℝ := 1 - 2 * M / r

/-- Equational form of `schwarzschildF M r`. -/
lemma schwarzschildF_eq (M r : ℝ) : schwarzschildF M r = 1 - 2 * M / r := rfl

/-- Clearing the radial denominator gives `r * schwarzschildF M r = r - 2 M`. -/
lemma r_mul_schwarzschildF (M r : ℝ) (hr : r ≠ 0) :
    r * schwarzschildF M r = r - 2 * M := by
  rw [schwarzschildF_eq]
  field_simp

/-- The Schwarzschild metric in `(t, r, θ, φ)` coordinates with signature `(-, +, +, +)`. -/
noncomputable def schwarzschildMetric (M : ℝ) (x : Fin 4 → ℝ) : Tensor2 4 :=
  StaticSpherical.staticSphericalMetric (schwarzschildF M) x

/-- The `tt` component of the Schwarzschild metric is `-(1 - 2M/r)`. -/
lemma schwarzschildMetric_tt (M : ℝ) (x : Fin 4 → ℝ) :
    schwarzschildMetric M x 0 0 = -(1 - 2 * M / x 1) := by
  simp [schwarzschildMetric, StaticSpherical.staticSphericalMetric, schwarzschildF]

/-- The static Newtonian potential is `Φ = -M / r`: `g_tt = -(1 + 2Φ)`. -/
lemma schwarzschildMetric_tt_potential (M : ℝ) (x : Fin 4 → ℝ) :
    schwarzschildMetric M x 0 0 = -(1 + 2 * (-M / x 1)) := by
  rw [schwarzschildMetric_tt]
  ring

/-- First radial derivative of the potential: `Φ' = M / r²`. -/
lemma potential_hasDerivAt (M r : ℝ) (hr : r ≠ 0) :
    HasDerivAt (fun s : ℝ => -M / s) (M / r ^ 2) r := by
  have h : HasDerivAt (fun s : ℝ => s⁻¹) (-(r ^ 2)⁻¹) r := hasDerivAt_inv hr
  have h' := h.const_mul (-M)
  have hfun : (fun s : ℝ => -M / s) = fun s : ℝ => -M * s⁻¹ := by
    funext s
    simp [div_eq_mul_inv]
  have hval : -M * -(r ^ 2)⁻¹ = M / r ^ 2 := by ring
  rw [← hfun, hval] at h'
  exact h'

/-- Second radial derivative of the potential: `Φ'' = -2M / r³`. -/
lemma potential_second_hasDerivAt (M r : ℝ) (hr : r ≠ 0) :
    HasDerivAt (fun s : ℝ => M / s ^ 2) (-2 * M / r ^ 3) r := by
  have hnum : HasDerivAt (fun _ : ℝ => M) 0 r := hasDerivAt_const r M
  have hden : HasDerivAt (fun s : ℝ => s ^ 2) (2 * r) r := by
    simpa using hasDerivAt_pow 2 r
  have h := hnum.div hden (pow_ne_zero 2 hr)
  have hfun : (fun s : ℝ => M / s ^ 2) = (fun _ : ℝ => M) / fun s : ℝ => s ^ 2 := rfl
  have hval : (0 * r ^ 2 - M * (2 * r)) / (r ^ 2) ^ 2 = -2 * M / r ^ 3 := by
    have hr2 : r ^ 2 ≠ 0 := pow_ne_zero 2 hr
    have hr4 : (r ^ 2) ^ 2 ≠ 0 := pow_ne_zero 2 hr2
    field_simp
    ring
  rw [← hfun, hval] at h
  exact h

/-- The `rr` component of the Schwarzschild metric is `f⁻¹`. -/
lemma schwarzschildMetric_rr (M : ℝ) (x : Fin 4 → ℝ) :
    schwarzschildMetric M x 1 1 = (schwarzschildF M (x 1))⁻¹ := by
  simp [schwarzschildMetric, StaticSpherical.staticSphericalMetric, schwarzschildF]

/-- `f ≠ 0` forces `r - 2M ≠ 0` away from `r = 0`. -/
lemma sub_ne_zero_of_ne (M r : ℝ) (hr : r ≠ 0) (hf : schwarzschildF M r ≠ 0) :
    r - 2 * M ≠ 0 := by
  intro h
  apply hf
  rw [schwarzschildF_eq]
  have h1 : 2 * M / r = 1 := by
    field_simp
    linarith
  rw [h1]
  ring

/-- Radial derivative of `f`: `∂_r (1 - 2M/r) = 2M / r²`. -/
lemma hasDerivAt_gtt (M r : ℝ) (hr : r ≠ 0) :
    HasDerivAt (fun s : ℝ => 1 - 2 * M / s) (2 * M / r ^ 2) r := by
  have h := HasDerivAt.sub (hasDerivAt_const r (1 : ℝ))
    ((hasDerivAt_inv hr).const_mul (2 * M))
  have hfun : (fun s : ℝ => 1 - 2 * M / s)
      = (fun _ : ℝ => 1) - fun s : ℝ => 2 * M * s⁻¹ := by
    funext s
    simp [div_eq_mul_inv]
  have hval : (0 : ℝ) - 2 * M * -(r ^ 2)⁻¹ = 2 * M / r ^ 2 := by
    rw [div_eq_mul_inv]
    ring
  rw [← hfun, hval] at h
  exact h

/-- Because `g_tt = -f` depends only on `r`, the general formula
`Γ^t_{tr} = (1/2) g^{tt} ∂_r g_{tt}` contracts `g^{tt} = -f⁻¹` against `-∂_r f = -2M/r²`, yielding
`M / (r² f)`. -/
lemma gammaTtr_from_metric (M r : ℝ) (hf : schwarzschildF M r ≠ 0) :
    (1 / 2 : ℝ) * (-(schwarzschildF M r)⁻¹) * (-(2 * M / r ^ 2))
      = M / (r ^ 2 * schwarzschildF M r) := by
  field_simp

/-- Radial derivative of `g_rr = f⁻¹`: `∂_r g_rr = -2M / (r - 2M)²`. -/
lemma deriv_grr (M r : ℝ) (hr : r ≠ 0) (hf : schwarzschildF M r ≠ 0) :
    deriv ((fun s : ℝ => 1 - 2 * M / s)⁻¹) r = -(2 * M) / (r - 2 * M) ^ 2 := by
  have hf' : (1 - 2 * M / r) ≠ 0 := by simpa [schwarzschildF_eq] using hf
  have h2 := sub_ne_zero_of_ne M r hr hf
  have h := HasDerivAt.inv (hasDerivAt_gtt M r hr) hf'
  rw [h.deriv]
  field_simp

/-- Contracting `g^{rr} = f` against the radial derivative `∂_r g_{rr} = ∂_r(f⁻¹) = -2M / (r - 2M)²`
in `Γ^r_{rr} = (1/2) g^{rr} ∂_r g_{rr}` cancels one factor of `f = (r - 2M)/r` to yield
`-M / (r (r - 2M))`. -/
lemma gammaRrr_from_metric (M r : ℝ) (hr : r ≠ 0) (hf : schwarzschildF M r ≠ 0) :
    (1 / 2 : ℝ) * (schwarzschildF M r) * (-(2 * M) / (r - 2 * M) ^ 2)
      = -M / (r * (r - 2 * M)) := by
  have h2 := sub_ne_zero_of_ne M r hr hf
  have hr_mul := r_mul_schwarzschildF M r hr
  field_simp [h2, hr]
  linear_combination -M * hr_mul

/-- Radial derivative of `Γ^t_{tr}`: `∂_r Γ^t_{tr} = -2M(r - M) / (r(r - 2M))²`. -/
lemma deriv_gammaTtr (M r : ℝ) (hr : r ≠ 0) (hf : schwarzschildF M r ≠ 0) :
    deriv (fun s : ℝ => M / (s ^ 2 * schwarzschildF M s)) r
      = -2 * M * (r - M) / (r * (r - 2 * M)) ^ 2 := by
  have hf' : (1 - 2 * M / r) ≠ 0 := by simpa [schwarzschildF_eq] using hf
  have h2 := sub_ne_zero_of_ne M r hr hf
  have hden : HasDerivAt (fun s : ℝ => s ^ 2 * (1 - 2 * M / s)) (2 * r - 2 * M) r := by
    have h1 : HasDerivAt (fun s : ℝ => s ^ 2) (2 * r) r := by
      simpa using hasDerivAt_pow 2 r
    have h2' : HasDerivAt (fun s : ℝ => 1 - 2 * M / s) (2 * M / r ^ 2) r :=
      hasDerivAt_gtt M r hr
    have hm := h1.mul h2'
    have hval : 2 * r * (1 - 2 * M / r) + r ^ 2 * (2 * M / r ^ 2) = 2 * r - 2 * M := by
      field_simp
      ring
    rw [hval] at hm
    exact hm
  have hdenne : r ^ 2 * (1 - 2 * M / r) ≠ 0 :=
    mul_ne_zero (pow_ne_zero 2 hr) hf'
  have h := HasDerivAt.div (hasDerivAt_const r M) hden hdenne
  have hfun : (fun s : ℝ => M / (s ^ 2 * schwarzschildF M s))
      = (fun _ : ℝ => M) / fun s : ℝ => s ^ 2 * (1 - 2 * M / s) := by
    funext s
    simp [schwarzschildF_eq]
  rw [hfun, h.deriv]
  field_simp
  ring

/-!

## B. Electric Riemann components and tidal eigenvalues

Contracting the derivatives and quadratic products of the Christoffel symbols evaluates the radial
and angular electric Riemann components, which in the static orthonormal frame recover the Newtonian
tidal field `diag(0, -2M/r³, M/r³, M/r³)`.

-/

/-- In the index formula `R^t{}_{rtr} = -∂_r Γ^t_{tr} + Γ^t_{tr} Γ^r_{rr} - (Γ^t_{tr})²` (where all
time derivatives vanish), the radial derivative of `Γ^t_{tr} = M/(r² f)` combines with the two
quadratic connection terms to produce `2M / (r³ f)`. -/
lemma riemann_t_rtr_from_metric (M r : ℝ) (hr : r ≠ 0) (hf : schwarzschildF M r ≠ 0) :
    -(deriv (fun s : ℝ => M / (s ^ 2 * schwarzschildF M s)) r)
      + (M / (r ^ 2 * schwarzschildF M r)) * (-M / (r * (r - 2 * M)))
      - (M / (r ^ 2 * schwarzschildF M r)) ^ 2
      = 2 * M / (r ^ 3 * schwarzschildF M r) := by
  have h2 := sub_ne_zero_of_ne M r hr hf
  rw [deriv_gammaTtr M r hr hf, schwarzschildF_eq]
  rw [schwarzschildF_eq] at hf
  field_simp [inv_eq_one_div]
  ring

/-- Lowering `R^t{}_{rtr}` with `g_tt = -f` gives `-2M / r³`, the radial entry of
`electricPart (M / r³)`. -/
lemma electric_r_from_metric (M r : ℝ) (hr : r ≠ 0) (hf : schwarzschildF M r ≠ 0) :
    -(schwarzschildF M r) * (2 * M / (r ^ 3 * schwarzschildF M r))
      = electricPart (M / r ^ 3) 1 1 := by
  have h11 : electricPart (M / r ^ 3) 1 1 = -(2 * M / r ^ 3) := by
    simp [electricPart]
    ring_nf
  rw [h11]
  field_simp

/-- `Γ^r_{θθ} = (1/2) g^{rr} (-∂_r g_{θθ}) = -r f`. -/
lemma gammaRthth_from_metric (M r : ℝ) :
    (1 / 2 : ℝ) * (schwarzschildF M r) * (-(2 * r)) = -(r * schwarzschildF M r) := by
  ring

/-- Since `∂_t Γ = ∂_θ Γ^t_{θθ} = 0` and only `Γ^r_{θθ}` enters the intermediate sum, the Riemann
formula simplifies to the single connection product `R^t{}_{θtθ} = Γ^t_{tr} Γ^r_{θθ} = -M / r`. -/
lemma riemann_t_thetatheta_from_metric (M r : ℝ) (hr : r ≠ 0)
    (hf : schwarzschildF M r ≠ 0) :
    (M / (r ^ 2 * schwarzschildF M r)) * (-(r * schwarzschildF M r)) = -M / r := by
  field_simp

/-- Orthonormal-frame `θθ` tidal eigenvalue: `M / r³`, the `(2, 2)` entry of
`electricPart (M / r³)`. -/
lemma electric_thetatheta_from_metric (M r : ℝ) (hr : r ≠ 0)
    (hf : schwarzschildF M r ≠ 0) :
    (schwarzschildF M r)⁻¹ * (r ^ 2)⁻¹ * (-(schwarzschildF M r) * (-M / r))
      = electricPart (M / r ^ 3) 2 2 := by
  have h22 : electricPart (M / r ^ 3) 2 2 = M / r ^ 3 := by
    simp [electricPart]
  rw [h22]
  field_simp

/-!

## C. Remaining independent Riemann components

Combining the angular metric derivatives `∂_r(r²)` and `∂_θ(r² sin²θ)` evaluates the azimuthal
and purely spatial Riemann components directly from the coordinate metric.

-/

/-- `Γ^r_{φφ} = (1/2) g^{rr} (-∂_r g_{φφ}) = -r f sin²θ`. -/
lemma gammaRphiphi_from_metric (M r th : ℝ) :
    (1 / 2 : ℝ) * (schwarzschildF M r) * (-(2 * r * Real.sin th ^ 2))
      = -(r * Real.sin th ^ 2 * schwarzschildF M r) := by
  ring

/-- By the azimuthal factor `sin²θ` in `g_{φφ} = r² sin²θ`, contracting `Γ^t_{tr} = M / (r² f)`
with `Γ^r_{φφ} = -r f sin²θ` in `R^t{}_{φtφ} = Γ^t_{tr} Γ^r_{φφ}` yields `-(M / r) sin²θ`. -/
lemma riemann_t_phitphi_from_metric (M r th : ℝ) (hr : r ≠ 0)
    (hf : schwarzschildF M r ≠ 0) :
    (M / (r ^ 2 * schwarzschildF M r))
        * (-(r * Real.sin th ^ 2 * schwarzschildF M r))
      = -(M / r) * Real.sin th ^ 2 := by
  field_simp

/-- Product `Γ^r_{rr} Γ^r_{θθ} = M / r`. -/
lemma gammaRrr_mul_gammaRthth (M r : ℝ) (hr : r ≠ 0)
    (hf : schwarzschildF M r ≠ 0) :
    (-M / (r ^ 2 * schwarzschildF M r)) * (-(r * schwarzschildF M r))
      = M / r := by
  field_simp

/-- Product `Γ^r_{θθ} Γ^θ_{rθ} = -f`. -/
lemma gammaRthth_mul_gammaThetar (M r : ℝ) (hr : r ≠ 0) :
    (-(r * schwarzschildF M r)) * (1 / r) = -schwarzschildF M r := by
  field_simp

/-- Evaluating `R^r{}_{θrθ} = ∂_r Γ^r_{θθ} + Γ^r_{rr} Γ^r_{θθ} - Γ^r_{θθ} Γ^θ_{rθ}` adds the
radial derivative `-f - r f'` of `Γ^r_{θθ} = -r f` to the two quadratic connection products to give
`-M / r`. -/
lemma riemann_r_thetar_from_metric (M r : ℝ) (hr : r ≠ 0)
    (hf : schwarzschildF M r ≠ 0) :
    (-(schwarzschildF M r) - 2 * M / r)
      + (-M / (r ^ 2 * schwarzschildF M r)) * (-(r * schwarzschildF M r))
      - (-(r * schwarzschildF M r)) * (1 / r)
      = -M / r := by
  rw [gammaRrr_mul_gammaRthth M r hr hf, gammaRthth_mul_gammaThetar M r hr]
  field_simp
  ring

/-- Product `Γ^r_{rr} Γ^r_{φφ} = (M / r) sin²θ`. -/
lemma gammaRrr_mul_gammaRphiphi (M r th : ℝ) (hr : r ≠ 0)
    (hf : schwarzschildF M r ≠ 0) :
    (-M / (r ^ 2 * schwarzschildF M r))
        * (-(r * Real.sin th ^ 2 * schwarzschildF M r))
      = (M / r) * Real.sin th ^ 2 := by
  field_simp

/-- Product `Γ^r_{φφ} Γ^φ_{rφ} = -f sin²θ`. -/
lemma gammaRphiphi_mul_gammaPhirphi (M r th : ℝ) (hr : r ≠ 0) :
    (-(r * Real.sin th ^ 2 * schwarzschildF M r)) * (1 / r)
      = -Real.sin th ^ 2 * schwarzschildF M r := by
  field_simp

/-- By spherical symmetry, the `(r, φ, r, φ)` component multiplies the `(r, θ, r, θ)` formula
`∂_r Γ^r_{φφ} + Γ^r_{rr} Γ^r_{φφ} - Γ^r_{φφ} Γ^φ_{rφ}` by `sin²θ` to yield `-(M / r) sin²θ`. -/
lemma riemann_r_phirphi_from_metric (M r th : ℝ) (hr : r ≠ 0)
    (hf : schwarzschildF M r ≠ 0) :
    (-(Real.sin th ^ 2) * (schwarzschildF M r + 2 * M / r))
      + (-M / (r ^ 2 * schwarzschildF M r))
          * (-(r * Real.sin th ^ 2 * schwarzschildF M r))
      - (-(r * Real.sin th ^ 2 * schwarzschildF M r)) * (1 / r)
      = -(M / r) * Real.sin th ^ 2 := by
  rw [gammaRrr_mul_gammaRphiphi M r th hr hf, gammaRphiphi_mul_gammaPhirphi M r th hr]
  field_simp
  ring

/-- `Γ^θ_{φφ} = (1/2) g^{θθ} (-∂_θ g_{φφ}) = -sin θ cos θ`. -/
lemma gammaThetaphiphi_from_metric (r th : ℝ) (hr : r ≠ 0) :
    (1 / 2 : ℝ) * (r ^ 2)⁻¹
        * (-(2 * r ^ 2 * Real.sin th * Real.cos th))
      = -(Real.sin th * Real.cos th) := by
  field_simp

/-- `Γ^φ_{θφ} = (1/2) g^{φφ} ∂_θ g_{φφ} = cos θ / sin θ`. -/
lemma gammaPhiphitheta_from_metric (r th : ℝ) (hr : r ≠ 0)
    (hsin : Real.sin th ≠ 0) :
    (1 / 2 : ℝ) * (r ^ 2 * Real.sin th ^ 2)⁻¹
        * (2 * r ^ 2 * Real.sin th * Real.cos th)
      = Real.cos th / Real.sin th := by
  field_simp

/-- Evaluating `R^θ{}_{φθφ} = ∂_θ Γ^θ_{φφ} + Γ^θ_{rθ} Γ^r_{φφ} - Γ^θ_{φφ} Γ^φ_{θφ}` combines the
angular curvature `1 - f(r)` of constant-`r` spheres with the metric lapse to give
`(2M / r) sin²θ`. -/
lemma riemann_theta_phitheta_from_metric (M r th : ℝ) (hr : r ≠ 0)
    (hsin : Real.sin th ≠ 0) :
    (Real.sin th ^ 2 - Real.cos th ^ 2)
      + (1 / r) * (-(r * Real.sin th ^ 2 * schwarzschildF M r))
      - (-(Real.sin th * Real.cos th)) * (Real.cos th / Real.sin th)
      = (2 * M / r) * Real.sin th ^ 2 := by
  rw [schwarzschildF_eq]
  field_simp
  ring

/-- Lowering `R^t{}_{φtφ}` with `g_tt = -f` gives `(M f / r) sin²θ`. -/
lemma rt_phitphi_lowered (M r th : ℝ) :
    -(schwarzschildF M r) * (-(M / r) * Real.sin th ^ 2)
      = (M * schwarzschildF M r / r) * Real.sin th ^ 2 := by
  ring

/-- Frame rescaling of `R_{tφtφ}` cancels the metric factors to give `M / r³`. -/
lemma frame_phiphi (M r th : ℝ) (hr : r ≠ 0) (hf : schwarzschildF M r ≠ 0)
    (hsin : Real.sin th ≠ 0) :
    (schwarzschildF M r)⁻¹ * (r ^ 2 * Real.sin th ^ 2)⁻¹
        * ((M * schwarzschildF M r / r) * Real.sin th ^ 2)
      = M / r ^ 3 := by
  have h1 : (schwarzschildF M r)⁻¹ * schwarzschildF M r = 1 :=
    inv_mul_cancel₀ hf
  have h2 : (r ^ 2 * Real.sin th ^ 2)⁻¹ * Real.sin th ^ 2 = 1 / r ^ 2 := by
    field_simp
  calc (schwarzschildF M r)⁻¹ * (r ^ 2 * Real.sin th ^ 2)⁻¹
        * ((M * schwarzschildF M r / r) * Real.sin th ^ 2)
      = ((schwarzschildF M r)⁻¹ * schwarzschildF M r)
          * ((r ^ 2 * Real.sin th ^ 2)⁻¹ * Real.sin th ^ 2) * (M / r) := by
        ring
    _ = 1 * (1 / r ^ 2) * (M / r) := by rw [h1, h2]
    _ = M / r ^ 3 := by
        field_simp

/-- Orthonormal-frame `φφ` tidal eigenvalue: `M / r³`, the `(3, 3)` entry of
`electricPart (M / r³)`. -/
lemma electric_phiphi_from_metric (M r th : ℝ) (hr : r ≠ 0)
    (hf : schwarzschildF M r ≠ 0) (hsin : Real.sin th ≠ 0) :
    (schwarzschildF M r)⁻¹ * (r ^ 2 * Real.sin th ^ 2)⁻¹
        * (M * schwarzschildF M r / r * Real.sin th ^ 2)
      = electricPart (M / r ^ 3) 3 3 := by
  have h33 : electricPart (M / r ^ 3) 3 3 = M / r ^ 3 := by
    simp [electricPart]
  rw [h33]
  exact frame_phiphi M r th hr hf hsin

/-!

## D. Assembled curvature and electric part statements

For convenient downstream matching, we package the orthonormal-frame tidal eigenvalues and the
remaining coordinate Riemann components into conjunctions.

-/

/-- The entire frame electric part of the Weyl tensor (`diag(0, -2M/r³, M/r³, M/r³)` plus all
seven vanishing entries) assembled from the Schwarzschild metric. -/
lemma electricPart_from_metric (M r th : ℝ) (hr : r ≠ 0)
    (hf : schwarzschildF M r ≠ 0) (hsin : Real.sin th ≠ 0) :
    (-(schwarzschildF M r) * (2 * M / (r ^ 3 * schwarzschildF M r))
        = electricPart (M / r ^ 3) 1 1)
      ∧ ((schwarzschildF M r)⁻¹ * (r ^ 2)⁻¹ * (-(schwarzschildF M r) * (-M / r))
          = electricPart (M / r ^ 3) 2 2)
      ∧ ((schwarzschildF M r)⁻¹ * (r ^ 2 * Real.sin th ^ 2)⁻¹
            * (M * schwarzschildF M r / r * Real.sin th ^ 2)
          = electricPart (M / r ^ 3) 3 3)
      ∧ electricPart (M / r ^ 3) 0 0 = 0
      ∧ electricPart (M / r ^ 3) 0 1 = 0
      ∧ electricPart (M / r ^ 3) 0 2 = 0
      ∧ electricPart (M / r ^ 3) 0 3 = 0
      ∧ electricPart (M / r ^ 3) 1 2 = 0
      ∧ electricPart (M / r ^ 3) 1 3 = 0
      ∧ electricPart (M / r ^ 3) 2 3 = 0 :=
  ⟨electric_r_from_metric M r hr hf,
   electric_thetatheta_from_metric M r hr hf,
   electric_phiphi_from_metric M r th hr hf hsin,
   by simp [electricPart], by simp [electricPart], by simp [electricPart],
   by simp [electricPart], by simp [electricPart], by simp [electricPart],
   by simp [electricPart]⟩

/-- The four remaining independent Schwarzschild Riemann components derived from the metric. -/
lemma riemann_components_from_metric (M r th : ℝ) (hr : r ≠ 0)
    (hf : schwarzschildF M r ≠ 0) (hsin : Real.sin th ≠ 0) :
    ((M / (r ^ 2 * schwarzschildF M r))
          * (-(r * Real.sin th ^ 2 * schwarzschildF M r))
        = -(M / r) * Real.sin th ^ 2)
      ∧ ((-(schwarzschildF M r) - 2 * M / r)
          + (-M / (r ^ 2 * schwarzschildF M r))
              * (-(r * schwarzschildF M r))
          - (-(r * schwarzschildF M r)) * (1 / r) = -M / r)
      ∧ ((-(Real.sin th ^ 2) * (schwarzschildF M r + 2 * M / r))
          + (-M / (r ^ 2 * schwarzschildF M r))
              * (-(r * Real.sin th ^ 2 * schwarzschildF M r))
          - (-(r * Real.sin th ^ 2 * schwarzschildF M r)) * (1 / r)
        = -(M / r) * Real.sin th ^ 2)
      ∧ ((Real.sin th ^ 2 - Real.cos th ^ 2)
          + (1 / r) * (-(r * Real.sin th ^ 2 * schwarzschildF M r))
          - (-(Real.sin th * Real.cos th)) * (Real.cos th / Real.sin th)
        = (2 * M / r) * Real.sin th ^ 2) :=
  ⟨riemann_t_phitphi_from_metric M r th hr hf,
   riemann_r_thetar_from_metric M r hr hf,
   riemann_r_phirphi_from_metric M r th hr hf,
   riemann_theta_phitheta_from_metric M r th hr hsin⟩

/-- The lapse function `f(r) = 1 - 2M / r` of a Schwarzschild spacetime. -/
noncomputable def SchwarzschildSpacetime.lapse (S : SchwarzschildSpacetime) (r : ℝ) : ℝ :=
  schwarzschildF S.M r

/-- The coordinate metric of a Schwarzschild spacetime in `(t, r, θ, φ)` coordinates. -/
noncomputable def SchwarzschildSpacetime.metric (S : SchwarzschildSpacetime)
    (x : Fin 4 → ℝ) : Tensor2 4 :=
  schwarzschildMetric S.M x

/-- With `M = r_s / 2`, the Schwarzschild lapse equals the exterior `g_tt` factor of the
incompressible fluid sphere, `1 - r_s / r`. -/
lemma schwarzschildF_of_incompressibleSphere (S : IncompressibleSphere) (r : ℝ) :
    schwarzschildF (S.rs / 2) r = S.gttOut r := by
  simp only [schwarzschildF, IncompressibleSphere.gttOut]
  ring

/-- The Schwarzschild `tt` metric component is minus the incompressible-sphere exterior `g_tt`
factor, reflecting the `(-, +, +, +)` signature used here. -/
lemma schwarzschildMetric_tt_of_incompressibleSphere (S : IncompressibleSphere)
    (x : Fin 4 → ℝ) :
    schwarzschildMetric (S.rs / 2) x 0 0 = -S.gttOut (x 1) := by
  rw [schwarzschildMetric_tt, ← schwarzschildF_of_incompressibleSphere]
  rfl

/-- The Schwarzschild `rr` metric component agrees with the incompressible-sphere exterior
`g_rr`. -/
lemma schwarzschildMetric_rr_of_incompressibleSphere (S : IncompressibleSphere)
    (x : Fin 4 → ℝ) :
    schwarzschildMetric (S.rs / 2) x 1 1 = S.grrOut (x 1) := by
  rw [schwarzschildMetric_rr, schwarzschildF_of_incompressibleSphere]
  simp [IncompressibleSphere.grrOut, IncompressibleSphere.gttOut]

end Schwarzschild

end GeneralRelativity
