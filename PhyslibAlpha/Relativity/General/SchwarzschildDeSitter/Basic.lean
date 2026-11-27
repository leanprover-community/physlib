/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import PhyslibAlpha.Relativity.General.Schwarzschild.Basic
public import PhyslibAlpha.Relativity.General.Schwarzschild.ElectricWeyl
public import PhyslibAlpha.Relativity.Metrics.StaticSphericalMetric.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!

# Schwarzschild–de Sitter curvature from the metric components

Derivation of the six independent Riemann curvature components and `Λ`-independent Weyl electric
eigenvalues directly from `SchwarzschildDeSitterSpacetime`.

## i. Overview

With radial metric function `f = 1 - 2M/r - Λr²/3` (`SchwarzschildDeSitterSpacetime.metricFn`)
and half-derivative `n = f'/2 = M/r² - Λr/3` (`SchwarzschildDeSitterSpacetime.metricFnHalfDeriv`),
the mixed radial Christoffel symbols are `Γ^t_{tr} = n / f` and `Γ^r_{rr} = -n / f`.
Differentiating these expressions yields all six independent Riemann components for general `Λ`:

- `R^t{}_{rtr} = (2M / r³ + Λ / 3) / f`,
- `R^t{}_{θtθ} = R^r{}_{θrθ} = Λ r² / 3 - M / r`,
- `R^t{}_{φtφ} = R^r{}_{φrφ} = (Λ r² / 3 - M / r) sin²θ`,
- `R^θ{}_{φθφ} = (2M / r + Λ r² / 3) sin²θ`.

Lowering into the orthonormal frame and subtracting the trace piece `-(Λ / 3) g` recovers
`electricPart (M / r³)` for every `Λ`: the cosmological constant shifts Ricci curvature while
leaving the Weyl tidal field unchanged.

## ii. Key results

- `SchwarzschildDeSitterSpacetime`, `SchwarzschildDeSitterSpacetime.metric`,
  `SchwarzschildDeSitterSpacetime.metricInv`, `SchwarzschildDeSitterSpacetime.toCoordinateMetric`,
  `SchwarzschildDeSitterSpacetime.metricFn`,
  `SchwarzschildDeSitterSpacetime.metricFnHalfDeriv` : Schwarzschild–de Sitter spacetime structure,
  coordinate metric, inverse, and metric function.
- `SchwarzschildDeSitterSpacetime.metricFn_zero_lambda` : reduction to
  `SchwarzschildSpacetime.metricFn` at `Λ = 0`.
- `SchwarzschildDeSitterSpacetime.riemann_t_rtr`,
  `SchwarzschildDeSitterSpacetime.riemann_t_thetatheta`,
  `SchwarzschildDeSitterSpacetime.riemann_t_phitphi`,
  `SchwarzschildDeSitterSpacetime.riemann_r_thetar`,
  `SchwarzschildDeSitterSpacetime.riemann_r_phirphi`,
  `SchwarzschildDeSitterSpacetime.riemann_theta_phitheta` : all six Riemann components for general
  `Λ`.
- `SchwarzschildDeSitterSpacetime.weyl_rr`, `SchwarzschildDeSitterSpacetime.weyl_thetatheta`,
  `SchwarzschildDeSitterSpacetime.weyl_phiphi` : `Λ`-independence of the Weyl electric eigenvalues.

## iii. Table of contents

- A. Metric function, half-derivative, and Christoffel symbols
- B. The six Riemann components for general `Λ`
- C. `Λ`-independence of the Weyl electric eigenvalues

## iv. References

* R. M. Wald, *General Relativity* (1984), Ch. 6 (Sec. 6.1) & Sec. 4.2.
  [ref: wald_1984_general_relativity]
* C. W. Misner, K. S. Thorne, and J. A. Wheeler, *Gravitation* (1973), Ch. 23 & Ch. 27.
  [ref: mtw_1973_gravitation]
* S. M. Carroll, *Lecture Notes on General Relativity* (1997), Ch. 7
  (https://arxiv.org/pdf/gr-qc/9712019#page=168). [ref: Carroll1997]
-/

@[expose] public section

namespace GeneralRelativity

namespace SchwarzschildDeSitter

/-!

## A. Metric function, half-derivative, and Christoffel symbols

The Kottler metric is determined by the radial metric function `f(r) = 1 - 2M/r - Λr²/3`, whose
half-derivative `n(r) = M/r² - Λr/3` governs all non-vanishing radial Christoffel symbols.

-/

/-- Schwarzschild–de Sitter (Kottler) spacetime parameterized by mass `M` and cosmological
constant `Λ`. -/
structure SchwarzschildDeSitterSpacetime where
  /-- Geometric mass parameter `M` (`G = c = 1`). -/
  M : ℝ
  /-- Cosmological constant `Λ`. -/
  Λ : ℝ

namespace SchwarzschildDeSitterSpacetime

/-- The Schwarzschild–de Sitter radial metric function `f(r) = 1 - 2M / r - Λ r² / 3`. -/
noncomputable def metricFn (S : SchwarzschildDeSitterSpacetime) (r : ℝ) : ℝ :=
  1 - 2 * S.M / r - S.Λ * r ^ 2 / 3

-- Factored out to avoid repeated factor-of-2 cancellation in Christoffel and Riemann expressions.
/-- Half the radial derivative of the metric function, `n = f'/2 = M / r² - Λ r / 3`. -/
noncomputable def metricFnHalfDeriv (S : SchwarzschildDeSitterSpacetime) (r : ℝ) : ℝ :=
  S.M / r ^ 2 - S.Λ * r / 3

/-- View a Schwarzschild–de Sitter spacetime as a `StaticSphericalMetric` with profile
`S.metricFn`. -/
noncomputable def toStaticSpherical (S : SchwarzschildDeSitterSpacetime) :
    StaticSpherical.StaticSphericalMetric :=
  ⟨S.metricFn⟩

/-- The underlying radial metric function of `S.toStaticSpherical` is `S.metricFn`. -/
@[simp]
lemma toStaticSpherical_metricFn (S : SchwarzschildDeSitterSpacetime) :
    S.toStaticSpherical.metricFn = S.metricFn := rfl

/-- The Schwarzschild–de Sitter metric as a `CoordinateMetric 4` on its regular chart, where the
radial metric function and `sin θ` are nonzero. -/
noncomputable def toCoordinateMetric (S : SchwarzschildDeSitterSpacetime) : CoordinateMetric 4 :=
  S.toStaticSpherical.toCoordinateMetric

/-- The Schwarzschild–de Sitter metric in `(t, r, θ, φ)` coordinates. -/
noncomputable def metric (S : SchwarzschildDeSitterSpacetime) (x : Fin 4 → ℝ) : Tensor2 4 :=
  S.toStaticSpherical.metric x

/-- The inverse of the Schwarzschild–de Sitter metric in `(t, r, θ, φ)` coordinates. -/
noncomputable def metricInv (S : SchwarzschildDeSitterSpacetime) (x : Fin 4 → ℝ) : Tensor2 4 :=
  S.toStaticSpherical.metricInv x

/-- The covariant field of `S.toCoordinateMetric` is `S.metric`. -/
@[simp] lemma toCoordinateMetric_g (S : SchwarzschildDeSitterSpacetime) :
    S.toCoordinateMetric.g = S.metric := rfl

/-- The inverse field of `S.toCoordinateMetric` is `S.metricInv`. -/
@[simp] lemma toCoordinateMetric_ginv (S : SchwarzschildDeSitterSpacetime) :
    S.toCoordinateMetric.ginv = S.metricInv := rfl

/-- At `Λ = 0`, the Kottler radial metric function reduces to the Schwarzschild metric
function. -/
lemma metricFn_zero_lambda (M r : ℝ) :
    (SchwarzschildDeSitterSpacetime.mk M 0).metricFn r =
      (Schwarzschild.SchwarzschildSpacetime.mk M).metricFn r := by
  simp [metricFn, Schwarzschild.SchwarzschildSpacetime.metricFn]

/-- `f = 1 - 2M/r - Λr²/3` is differentiable away from `r = 0` with `f' = 2 n`. -/
lemma hasDerivAt_metricFn (S : SchwarzschildDeSitterSpacetime) (r : ℝ) (hr : r ≠ 0) :
    HasDerivAt S.metricFn (2 * S.metricFnHalfDeriv r) r := by
  have h1 : HasDerivAt (fun s : ℝ => 1 - 2 * S.M / s) (2 * S.M / r ^ 2) r :=
    (Schwarzschild.SchwarzschildSpacetime.mk S.M).hasDerivAt_metricFn r hr
  have h2 : HasDerivAt (fun s : ℝ => S.Λ / 3 * s ^ 2) (S.Λ / 3 * (2 * r)) r := by
    have h := (hasDerivAt_pow 2 r).const_mul (S.Λ / 3)
    simpa using h
  have h := h1.sub h2
  have hfun : S.metricFn
      = (fun s : ℝ => 1 - 2 * S.M / s) - fun s : ℝ => S.Λ / 3 * s ^ 2 := by
    funext s
    simp [metricFn, Pi.sub_apply]
    ring
  have hval : 2 * S.M / r ^ 2 - S.Λ / 3 * (2 * r) = 2 * S.metricFnHalfDeriv r := by
    simp [metricFnHalfDeriv]
    ring
  rw [← hfun, hval] at h
  exact h

/-- `f' = 2 n` as an identity for `deriv`. -/
lemma deriv_metricFn (S : SchwarzschildDeSitterSpacetime) (r : ℝ) (hr : r ≠ 0) :
    deriv S.metricFn r = 2 * S.metricFnHalfDeriv r :=
  (S.hasDerivAt_metricFn r hr).deriv

/-- `n = M/r² - Λr/3` is differentiable away from `r = 0` with `n' = -2M/r³ - Λ/3`. -/
lemma hasDerivAt_metricFnHalfDeriv (S : SchwarzschildDeSitterSpacetime) (r : ℝ) (hr : r ≠ 0) :
    HasDerivAt S.metricFnHalfDeriv (-2 * S.M / r ^ 3 - S.Λ / 3) r := by
  have h1 : HasDerivAt (fun s : ℝ => S.M / s ^ 2) (-2 * S.M / r ^ 3) r :=
    (Schwarzschild.SchwarzschildSpacetime.mk S.M).potential_second_hasDerivAt r hr
  have h2 : HasDerivAt (fun s : ℝ => S.Λ / 3 * s) (S.Λ / 3) r := by
    simpa using (hasDerivAt_id r).const_mul (S.Λ / 3)
  have h := h1.sub h2
  have hfun : S.metricFnHalfDeriv
      = (fun s : ℝ => S.M / s ^ 2) - fun s : ℝ => S.Λ / 3 * s := by
    funext s
    simp [metricFnHalfDeriv, Pi.sub_apply]
    ring
  rw [← hfun] at h
  exact h

/-- `n' = -2M/r³ - Λ/3` as an identity for `deriv`. -/
lemma deriv_metricFnHalfDeriv (S : SchwarzschildDeSitterSpacetime) (r : ℝ) (hr : r ≠ 0) :
    deriv S.metricFnHalfDeriv r = -2 * S.M / r ^ 3 - S.Λ / 3 :=
  (S.hasDerivAt_metricFnHalfDeriv r hr).deriv

/-- Radial derivative of the ratio `n / f = Γ^t_{tr}`. -/
lemma deriv_metricFnHalfDeriv_div_metricFn (S : SchwarzschildDeSitterSpacetime) (r : ℝ)
    (hr : r ≠ 0) (hf : S.metricFn r ≠ 0) :
    deriv (fun s : ℝ => S.metricFnHalfDeriv s / S.metricFn s) r
      = (-2 * S.M / r ^ 3 - S.Λ / 3) / S.metricFn r
          - S.metricFnHalfDeriv r * (2 * S.metricFnHalfDeriv r) / (S.metricFn r) ^ 2 := by
  have h := (S.hasDerivAt_metricFnHalfDeriv r hr).div (S.hasDerivAt_metricFn r hr) hf
  have hfun : (fun s : ℝ => S.metricFnHalfDeriv s / S.metricFn s) =
      S.metricFnHalfDeriv / S.metricFn := rfl
  rw [hfun, h.deriv]
  field_simp [hf]

/-- `Γ^t_{tr} = (1/2) g^{tt} ∂_r g_{tt} = n / f`. -/
lemma christoffelTtr (S : SchwarzschildDeSitterSpacetime) (r : ℝ) (hf : S.metricFn r ≠ 0) :
    (1 / 2 : ℝ) * (-(S.metricFn r)⁻¹) * (-(2 * S.metricFnHalfDeriv r))
      = S.metricFnHalfDeriv r / S.metricFn r := by
  field_simp [hf]

/-- `∂_r (f⁻¹) = -2 n / f²`. -/
lemma deriv_metricFn_inv (S : SchwarzschildDeSitterSpacetime) (r : ℝ) (hr : r ≠ 0)
    (hf : S.metricFn r ≠ 0) :
    deriv (fun s : ℝ => (S.metricFn s)⁻¹) r
      = -(2 * S.metricFnHalfDeriv r) / (S.metricFn r) ^ 2 :=
  (S.hasDerivAt_metricFn r hr).inv hf |>.deriv

/-- `Γ^r_{rr} = (1/2) g^{rr} ∂_r g_{rr} = -n / f`. -/
lemma christoffelRrr (S : SchwarzschildDeSitterSpacetime) (r : ℝ) (hr : r ≠ 0)
    (hf : S.metricFn r ≠ 0) :
    (1 / 2 : ℝ) * (S.metricFn r) * deriv (fun s : ℝ => (S.metricFn s)⁻¹) r
      = -S.metricFnHalfDeriv r / S.metricFn r := by
  rw [S.deriv_metricFn_inv r hr hf]
  field_simp [hf]

/-- `Γ^r_{θθ} = -r f`. -/
lemma christoffelRThetaTheta (S : SchwarzschildDeSitterSpacetime) (r : ℝ) :
    (1 / 2 : ℝ) * (S.metricFn r) * (-(2 * r)) = -(r * S.metricFn r) := by
  ring

/-- `Γ^r_{φφ} = -r f sin²θ`. -/
lemma christoffelRPhiPhi (S : SchwarzschildDeSitterSpacetime) (r th : ℝ) :
    (1 / 2 : ℝ) * (S.metricFn r) * (-(2 * r * Real.sin th ^ 2))
      = -(r * Real.sin th ^ 2 * S.metricFn r) := by
  ring

/-!

## B. The six Riemann components for general `Λ`

Each independent Riemann curvature component combines the Kottler mass potential `-M/r` with the
cosmological constant contribution `Λr²/3`.

-/

/-- Equational form of `SchwarzschildDeSitterSpacetime.metricFn`. -/
lemma metricFn_eq (S : SchwarzschildDeSitterSpacetime) (r : ℝ) :
    S.metricFn r = 1 - 2 * S.M / r - S.Λ * r ^ 2 / 3 := rfl

/-- Equational form of `SchwarzschildDeSitterSpacetime.metricFnHalfDeriv`. -/
lemma metricFnHalfDeriv_eq (S : SchwarzschildDeSitterSpacetime) (r : ℝ) :
    S.metricFnHalfDeriv r = S.M / r ^ 2 - S.Λ * r / 3 := rfl

/-- The `t r t r` Riemann component for Schwarzschild–de Sitter: `(2M/r³ + Λ/3)/f`. -/
lemma riemann_t_rtr (S : SchwarzschildDeSitterSpacetime) (r : ℝ) (hr : r ≠ 0)
    (hf : S.metricFn r ≠ 0) :
    -(deriv (fun s : ℝ => S.metricFnHalfDeriv s / S.metricFn s) r)
      + (S.metricFnHalfDeriv r / S.metricFn r) * (-(S.metricFnHalfDeriv r / S.metricFn r))
      - (S.metricFnHalfDeriv r / S.metricFn r) ^ 2
      = (2 * S.M / r ^ 3 + S.Λ / 3) / S.metricFn r := by
  rw [S.deriv_metricFnHalfDeriv_div_metricFn r hr hf]
  field_simp [hf, hr]
  ring

/-- The `t θ t θ` Riemann component for Schwarzschild–de Sitter: `Λ r² / 3 - M / r`. -/
lemma riemann_t_thetatheta (S : SchwarzschildDeSitterSpacetime) (r : ℝ) (hr : r ≠ 0)
    (hf : S.metricFn r ≠ 0) :
    (S.metricFnHalfDeriv r / S.metricFn r) * (-(r * S.metricFn r))
      = S.Λ * r ^ 2 / 3 - S.M / r := by
  rw [metricFnHalfDeriv_eq]
  field_simp [hf, hr]
  ring

/-- The `t φ t φ` Riemann component for Schwarzschild–de Sitter: `(Λ r² / 3 - M / r) sin²θ`. -/
lemma riemann_t_phitphi (S : SchwarzschildDeSitterSpacetime) (r th : ℝ) (hr : r ≠ 0)
    (hf : S.metricFn r ≠ 0) :
    (S.metricFnHalfDeriv r / S.metricFn r) * (-(r * Real.sin th ^ 2 * S.metricFn r))
      = (S.Λ * r ^ 2 / 3 - S.M / r) * Real.sin th ^ 2 := by
  rw [metricFnHalfDeriv_eq]
  field_simp [hf, hr]
  ring

/-- The `r θ r θ` Riemann component for Schwarzschild–de Sitter: `Λ r² / 3 - M / r`. -/
lemma riemann_r_thetar (S : SchwarzschildDeSitterSpacetime) (r : ℝ) (hr : r ≠ 0)
    (hf : S.metricFn r ≠ 0) :
    (-(S.metricFn r) - r * (2 * S.metricFnHalfDeriv r))
      + (-(S.metricFnHalfDeriv r) / S.metricFn r) * (-(r * S.metricFn r))
      - (-(r * S.metricFn r)) * (1 / r)
      = S.Λ * r ^ 2 / 3 - S.M / r := by
  rw [metricFnHalfDeriv_eq]
  field_simp [hf, hr]
  ring

/-- The `r φ r φ` Riemann component for Schwarzschild–de Sitter: `(Λ r² / 3 - M / r) sin²θ`. -/
lemma riemann_r_phirphi (S : SchwarzschildDeSitterSpacetime) (r th : ℝ) (hr : r ≠ 0)
    (hf : S.metricFn r ≠ 0) :
    (-(S.metricFn r) - r * (2 * S.metricFnHalfDeriv r)) * Real.sin th ^ 2
      + (-(S.metricFnHalfDeriv r) / S.metricFn r) * (-(r * Real.sin th ^ 2 * S.metricFn r))
      - (-(r * Real.sin th ^ 2 * S.metricFn r)) * (1 / r)
      = (S.Λ * r ^ 2 / 3 - S.M / r) * Real.sin th ^ 2 := by
  rw [metricFnHalfDeriv_eq]
  field_simp [hf, hr]
  ring

/-- The `θ φ θ φ` Riemann component for Schwarzschild–de Sitter: `(2M/r + Λr²/3) sin²θ`. -/
lemma riemann_theta_phitheta (S : SchwarzschildDeSitterSpacetime) (r th : ℝ) (hr : r ≠ 0)
    (hsin : Real.sin th ≠ 0) :
    (Real.sin th ^ 2 - Real.cos th ^ 2)
      + (1 / r) * (-(r * Real.sin th ^ 2 * S.metricFn r))
      - (-(Real.sin th * Real.cos th)) * (Real.cos th / Real.sin th)
      = (2 * S.M / r + S.Λ * r ^ 2 / 3) * Real.sin th ^ 2 := by
  rw [metricFn_eq]
  field_simp [hr, hsin]
  ring

/-- All six independent Schwarzschild–de Sitter Riemann components assembled as one
conjunction. -/
lemma riemann_components (S : SchwarzschildDeSitterSpacetime) (r th : ℝ) (hr : r ≠ 0)
    (hf : S.metricFn r ≠ 0) (hsin : Real.sin th ≠ 0) :
    (-(deriv (fun s : ℝ => S.metricFnHalfDeriv s / S.metricFn s) r)
        + (S.metricFnHalfDeriv r / S.metricFn r) * (-(S.metricFnHalfDeriv r / S.metricFn r))
        - (S.metricFnHalfDeriv r / S.metricFn r) ^ 2
        = (2 * S.M / r ^ 3 + S.Λ / 3) / S.metricFn r)
      ∧ ((S.metricFnHalfDeriv r / S.metricFn r) * (-(r * S.metricFn r))
          = S.Λ * r ^ 2 / 3 - S.M / r)
      ∧ ((S.metricFnHalfDeriv r / S.metricFn r) * (-(r * Real.sin th ^ 2 * S.metricFn r))
          = (S.Λ * r ^ 2 / 3 - S.M / r) * Real.sin th ^ 2)
      ∧ ((-(S.metricFn r) - r * (2 * S.metricFnHalfDeriv r))
            + (-(S.metricFnHalfDeriv r) / S.metricFn r) * (-(r * S.metricFn r))
            - (-(r * S.metricFn r)) * (1 / r) = S.Λ * r ^ 2 / 3 - S.M / r)
      ∧ ((-(S.metricFn r) - r * (2 * S.metricFnHalfDeriv r)) * Real.sin th ^ 2
            + (-(S.metricFnHalfDeriv r) / S.metricFn r) *
                (-(r * Real.sin th ^ 2 * S.metricFn r))
            - (-(r * Real.sin th ^ 2 * S.metricFn r)) * (1 / r)
          = (S.Λ * r ^ 2 / 3 - S.M / r) * Real.sin th ^ 2)
      ∧ ((Real.sin th ^ 2 - Real.cos th ^ 2)
            + (1 / r) * (-(r * Real.sin th ^ 2 * S.metricFn r))
            - (-(Real.sin th * Real.cos th)) * (Real.cos th / Real.sin th)
          = (2 * S.M / r + S.Λ * r ^ 2 / 3) * Real.sin th ^ 2) :=
  ⟨S.riemann_t_rtr r hr hf,
   S.riemann_t_thetatheta r hr hf,
   S.riemann_t_phitphi r th hr hf,
   S.riemann_r_thetar r hr hf,
   S.riemann_r_phirphi r th hr hf,
   S.riemann_theta_phitheta r th hr hsin⟩

/-!

## C. `Λ`-independence of the Weyl electric eigenvalues

Subtracting the isotropic cosmological trace part `(Λ / 3) g` in the orthonormal frame isolates
the pure Weyl tidal tensor `electricPart (M / r³)`, demonstrating that `Λ` does not affect local
tidal stretching.

-/

/-- The radial Weyl electric eigenvalue `-f R^t{}_{rtr} + Λ/3 = -2M/r³` is independent of `Λ`. -/
lemma weyl_rr (S : SchwarzschildDeSitterSpacetime) (r : ℝ) (hf : S.metricFn r ≠ 0) :
    -(S.metricFn r) * ((2 * S.M / r ^ 3 + S.Λ / 3) / S.metricFn r) + S.Λ / 3
      = Schwarzschild.electricPart (S.M / r ^ 3) 1 1 := by
  have h11 : Schwarzschild.electricPart (S.M / r ^ 3) 1 1 = -(2 * S.M / r ^ 3) := by
    simp [Schwarzschild.electricPart]
    ring
  rw [h11]
  field_simp [hf]
  ring

/-- The `θ` Weyl electric eigenvalue `f⁻¹ r⁻² (-f) (Λr²/3 - M/r) + Λ/3 = M/r³` is independent
of `Λ`. -/
lemma weyl_thetatheta (S : SchwarzschildDeSitterSpacetime) (r : ℝ) (hr : r ≠ 0)
    (hf : S.metricFn r ≠ 0) :
    (S.metricFn r)⁻¹ * (r ^ 2)⁻¹ * (-(S.metricFn r) * (S.Λ * r ^ 2 / 3 - S.M / r))
      + S.Λ / 3 = Schwarzschild.electricPart (S.M / r ^ 3) 2 2 := by
  have h22 : Schwarzschild.electricPart (S.M / r ^ 3) 2 2 = S.M / r ^ 3 := by
    simp [Schwarzschild.electricPart]
  rw [h22]
  field_simp [hr, hf]
  ring

/-- The `φ` Weyl electric eigenvalue equals `M/r³` for every `Λ`. -/
lemma weyl_phiphi (S : SchwarzschildDeSitterSpacetime) (r th : ℝ) (hr : r ≠ 0)
    (hf : S.metricFn r ≠ 0) (hsin : Real.sin th ≠ 0) :
    (S.metricFn r)⁻¹ * (r ^ 2 * Real.sin th ^ 2)⁻¹
        * (-(S.metricFn r) * ((S.Λ * r ^ 2 / 3 - S.M / r) * Real.sin th ^ 2))
      + S.Λ / 3 = Schwarzschild.electricPart (S.M / r ^ 3) 3 3 := by
  have h33 : Schwarzschild.electricPart (S.M / r ^ 3) 3 3 = S.M / r ^ 3 := by
    simp [Schwarzschild.electricPart]
  rw [h33]
  field_simp [hr, hf, hsin]
  ring

end SchwarzschildDeSitterSpacetime

end SchwarzschildDeSitter

end GeneralRelativity
