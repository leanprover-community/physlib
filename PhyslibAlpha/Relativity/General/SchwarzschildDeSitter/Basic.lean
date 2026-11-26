/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import PhyslibAlpha.Relativity.General.Schwarzschild.Basic
public import PhyslibAlpha.Relativity.General.SchwarzschildDeSitter.DeSitterFrame
public import PhyslibAlpha.Relativity.Metrics.StaticSphericalMetric
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

With lapse `f = 1 - 2M/r - Λr²/3` (`SchwarzschildDeSitterSpacetime.lapse`) and half-derivative
`n = f'/2 = M/r² - Λr/3` (`SchwarzschildDeSitterSpacetime.lapseHalfDeriv`), the mixed radial
Christoffel symbols are `Γ^t_{tr} = n / f` and `Γ^r_{rr} = -n / f`. Differentiating these
expressions yields all six independent Riemann components for general `Λ`:

- `R^t{}_{rtr} = (2M / r³ + Λ / 3) / f`,
- `R^t{}_{θtθ} = R^r{}_{θrθ} = Λ r² / 3 - M / r`,
- `R^t{}_{φtφ} = R^r{}_{φrφ} = (Λ r² / 3 - M / r) sin²θ`,
- `R^θ{}_{φθφ} = (2M / r + Λ r² / 3) sin²θ`.

Lowered into the orthonormal frame and subtracting the trace piece `-(Λ / 3) g` recovers
`electricPart (M / r³)` for every `Λ`: the cosmological constant shifts Ricci curvature while
leaving the Weyl tidal field unchanged.

## ii. Key results

- `SchwarzschildDeSitterSpacetime`, `SchwarzschildDeSitterSpacetime.metric`,
  `SchwarzschildDeSitterSpacetime.metricInv`, `SchwarzschildDeSitterSpacetime.lapse`,
  `SchwarzschildDeSitterSpacetime.lapseHalfDeriv` : Schwarzschild–de Sitter spacetime structure,
  coordinate metric, inverse, and lapse.
- `SchwarzschildDeSitterSpacetime.lapse_zero_lambda` : reduction to `SchwarzschildSpacetime.lapse`
  at `Λ = 0`.
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

- A. Lapse function, half-derivative, and Christoffel symbols
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

## A. Lapse function, half-derivative, and Christoffel symbols

-/

/-- Schwarzschild–de Sitter (Kottler) spacetime parameterized by mass `M` and cosmological
constant `Λ`. -/
structure SchwarzschildDeSitterSpacetime where
  /-- Geometric mass parameter `M` (`G = c = 1`). -/
  M : ℝ
  /-- Cosmological constant `Λ`. -/
  Λ : ℝ

namespace SchwarzschildDeSitterSpacetime

/-- The Schwarzschild–de Sitter lapse function `f = 1 - 2M / r - Λ r² / 3`. -/
noncomputable def lapse (S : SchwarzschildDeSitterSpacetime) (r : ℝ) : ℝ :=
  1 - 2 * S.M / r - S.Λ * r ^ 2 / 3

/-- Half the radial derivative of the lapse, `n = f'/2 = M / r² - Λ r / 3`, factored out so
rational Christoffel and Riemann component expressions avoid repeated factor-of-2 cancellation. -/
noncomputable def lapseHalfDeriv (S : SchwarzschildDeSitterSpacetime) (r : ℝ) : ℝ :=
  S.M / r ^ 2 - S.Λ * r / 3

/-- View a Schwarzschild–de Sitter spacetime as a `StaticSphericalMetric` with profile
`S.lapse`. -/
noncomputable def toStaticSpherical (S : SchwarzschildDeSitterSpacetime) :
    StaticSpherical.StaticSphericalMetric :=
  ⟨S.lapse⟩

/-- The Schwarzschild–de Sitter metric in `(t, r, θ, φ)` coordinates. -/
noncomputable def metric (S : SchwarzschildDeSitterSpacetime) (x : Fin 4 → ℝ) : Tensor2 4 :=
  S.toStaticSpherical.metric x

/-- The inverse of the Schwarzschild–de Sitter metric in `(t, r, θ, φ)` coordinates. -/
noncomputable def metricInv (S : SchwarzschildDeSitterSpacetime) (x : Fin 4 → ℝ) : Tensor2 4 :=
  S.toStaticSpherical.metricInv x

/-- At `Λ = 0`, the de Sitter lapse reduces to the Schwarzschild lapse. -/
lemma lapse_zero_lambda (M r : ℝ) :
    (SchwarzschildDeSitterSpacetime.mk M 0).lapse r =
      (Schwarzschild.SchwarzschildSpacetime.mk M).lapse r := by
  simp [lapse, Schwarzschild.SchwarzschildSpacetime.lapse]

/-- `f = 1 - 2M/r - Λr²/3` is differentiable away from `r = 0` with `f' = 2 n`. -/
lemma hasDerivAt_lapse (S : SchwarzschildDeSitterSpacetime) (r : ℝ) (hr : r ≠ 0) :
    HasDerivAt S.lapse (2 * S.lapseHalfDeriv r) r := by
  have h1 : HasDerivAt (fun s : ℝ => 1 - 2 * S.M / s) (2 * S.M / r ^ 2) r :=
    (Schwarzschild.SchwarzschildSpacetime.mk S.M).hasDerivAt_lapse r hr
  have h2 : HasDerivAt (fun s : ℝ => S.Λ / 3 * s ^ 2) (S.Λ / 3 * (2 * r)) r := by
    have h := (hasDerivAt_pow 2 r).const_mul (S.Λ / 3)
    simpa using h
  have h := h1.sub h2
  have hfun : S.lapse
      = (fun s : ℝ => 1 - 2 * S.M / s) - fun s : ℝ => S.Λ / 3 * s ^ 2 := by
    funext s
    simp [lapse, Pi.sub_apply]
    ring
  have hval : 2 * S.M / r ^ 2 - S.Λ / 3 * (2 * r) = 2 * S.lapseHalfDeriv r := by
    simp [lapseHalfDeriv]
    ring
  rw [← hfun, hval] at h
  exact h

/-- `f' = 2 n` as an identity for `deriv`. -/
lemma deriv_lapse (S : SchwarzschildDeSitterSpacetime) (r : ℝ) (hr : r ≠ 0) :
    deriv S.lapse r = 2 * S.lapseHalfDeriv r :=
  (S.hasDerivAt_lapse r hr).deriv

/-- `n = M/r² - Λr/3` is differentiable away from `r = 0` with `n' = -2M/r³ - Λ/3`. -/
lemma hasDerivAt_lapseHalfDeriv (S : SchwarzschildDeSitterSpacetime) (r : ℝ) (hr : r ≠ 0) :
    HasDerivAt S.lapseHalfDeriv (-2 * S.M / r ^ 3 - S.Λ / 3) r := by
  have h1 : HasDerivAt (fun s : ℝ => S.M / s ^ 2) (-2 * S.M / r ^ 3) r :=
    (Schwarzschild.SchwarzschildSpacetime.mk S.M).potential_second_hasDerivAt r hr
  have h2 : HasDerivAt (fun s : ℝ => S.Λ / 3 * s) (S.Λ / 3) r := by
    simpa using (hasDerivAt_id r).const_mul (S.Λ / 3)
  have h := h1.sub h2
  have hfun : S.lapseHalfDeriv
      = (fun s : ℝ => S.M / s ^ 2) - fun s : ℝ => S.Λ / 3 * s := by
    funext s
    simp [lapseHalfDeriv, Pi.sub_apply]
    ring
  rw [← hfun] at h
  exact h

/-- `n' = -2M/r³ - Λ/3` as an identity for `deriv`. -/
lemma deriv_lapseHalfDeriv (S : SchwarzschildDeSitterSpacetime) (r : ℝ) (hr : r ≠ 0) :
    deriv S.lapseHalfDeriv r = -2 * S.M / r ^ 3 - S.Λ / 3 :=
  (S.hasDerivAt_lapseHalfDeriv r hr).deriv

/-- `Γ^t_{tr} = (1/2) g^{tt} ∂_r g_{tt} = n / f`. -/
lemma gammaTtr (S : SchwarzschildDeSitterSpacetime) (r : ℝ) (hf : S.lapse r ≠ 0) :
    (1 / 2 : ℝ) * (-(S.lapse r)⁻¹) * (-(2 * S.lapseHalfDeriv r))
      = S.lapseHalfDeriv r / S.lapse r := by
  field_simp [hf]

/-- `∂_r (f⁻¹) = -2 n / f²`. -/
lemma deriv_lapse_inv (S : SchwarzschildDeSitterSpacetime) (r : ℝ) (hr : r ≠ 0)
    (hf : S.lapse r ≠ 0) :
    deriv (fun s : ℝ => (S.lapse s)⁻¹) r
      = -(2 * S.lapseHalfDeriv r) / (S.lapse r) ^ 2 :=
  (S.hasDerivAt_lapse r hr).inv hf |>.deriv

/-- `Γ^r_{rr} = (1/2) g^{rr} ∂_r g_{rr} = -n / f`. -/
lemma gammaRrr (S : SchwarzschildDeSitterSpacetime) (r : ℝ) (hr : r ≠ 0) (hf : S.lapse r ≠ 0) :
    (1 / 2 : ℝ) * (S.lapse r) * deriv (fun s : ℝ => (S.lapse s)⁻¹) r
      = -S.lapseHalfDeriv r / S.lapse r := by
  rw [S.deriv_lapse_inv r hr hf]
  field_simp [hf]

/-- `Γ^r_{θθ} = -r f`. -/
lemma gammaRthth (S : SchwarzschildDeSitterSpacetime) (r : ℝ) :
    (1 / 2 : ℝ) * (S.lapse r) * (-(2 * r)) = -(r * S.lapse r) := by
  ring

/-- `Γ^r_{φφ} = -r f sin²θ`. -/
lemma gammaRphiphi (S : SchwarzschildDeSitterSpacetime) (r th : ℝ) :
    (1 / 2 : ℝ) * (S.lapse r) * (-(2 * r * Real.sin th ^ 2))
      = -(r * Real.sin th ^ 2 * S.lapse r) := by
  ring

/-!

## B. The six Riemann components for general `Λ`

-/

/-- Equational form of `SchwarzschildDeSitterSpacetime.lapse`. -/
lemma lapse_eq (S : SchwarzschildDeSitterSpacetime) (r : ℝ) :
    S.lapse r = 1 - 2 * S.M / r - S.Λ * r ^ 2 / 3 := rfl

/-- Equational form of `SchwarzschildDeSitterSpacetime.lapseHalfDeriv`. -/
lemma lapseHalfDeriv_eq (S : SchwarzschildDeSitterSpacetime) (r : ℝ) :
    S.lapseHalfDeriv r = S.M / r ^ 2 - S.Λ * r / 3 := rfl

/-- The `t r t r` Riemann component for Schwarzschild–de Sitter: `(2M/r³ + Λ/3)/f`. -/
lemma riemann_t_rtr (S : SchwarzschildDeSitterSpacetime) (r : ℝ) (hr : r ≠ 0)
    (hf : S.lapse r ≠ 0) :
    -(deriv (fun s : ℝ => S.lapseHalfDeriv s / S.lapse s) r)
      + (S.lapseHalfDeriv r / S.lapse r) * (-(S.lapseHalfDeriv r / S.lapse r))
      - (S.lapseHalfDeriv r / S.lapse r) ^ 2
      = (2 * S.M / r ^ 3 + S.Λ / 3) / S.lapse r := by
  have hq : deriv (fun s : ℝ => S.lapseHalfDeriv s / S.lapse s) r
      = (-2 * S.M / r ^ 3 - S.Λ / 3) / S.lapse r
          - S.lapseHalfDeriv r * (2 * S.lapseHalfDeriv r) / (S.lapse r) ^ 2 := by
    have h := (S.hasDerivAt_lapseHalfDeriv r hr).div (S.hasDerivAt_lapse r hr) hf
    have hfun : (fun s : ℝ => S.lapseHalfDeriv s / S.lapse s) = S.lapseHalfDeriv / S.lapse := rfl
    rw [hfun, h.deriv]
    field_simp [hf]
  rw [hq]
  field_simp [hf, hr]
  ring

/-- The `t θ t θ` Riemann component for Schwarzschild–de Sitter: `Λ r² / 3 - M / r`. -/
lemma riemann_t_thetatheta (S : SchwarzschildDeSitterSpacetime) (r : ℝ) (hr : r ≠ 0)
    (hf : S.lapse r ≠ 0) :
    (S.lapseHalfDeriv r / S.lapse r) * (-(r * S.lapse r))
      = S.Λ * r ^ 2 / 3 - S.M / r := by
  rw [lapseHalfDeriv_eq]
  field_simp [hf, hr]
  ring

/-- The `t φ t φ` Riemann component for Schwarzschild–de Sitter: `(Λ r² / 3 - M / r) sin²θ`. -/
lemma riemann_t_phitphi (S : SchwarzschildDeSitterSpacetime) (r th : ℝ) (hr : r ≠ 0)
    (hf : S.lapse r ≠ 0) :
    (S.lapseHalfDeriv r / S.lapse r) * (-(r * Real.sin th ^ 2 * S.lapse r))
      = (S.Λ * r ^ 2 / 3 - S.M / r) * Real.sin th ^ 2 := by
  rw [lapseHalfDeriv_eq]
  field_simp [hf, hr]
  ring

/-- The `r θ r θ` Riemann component for Schwarzschild–de Sitter: `Λ r² / 3 - M / r`. -/
lemma riemann_r_thetar (S : SchwarzschildDeSitterSpacetime) (r : ℝ) (hr : r ≠ 0)
    (hf : S.lapse r ≠ 0) :
    (-(S.lapse r) - r * (2 * S.lapseHalfDeriv r))
      + (-(S.lapseHalfDeriv r) / S.lapse r) * (-(r * S.lapse r))
      - (-(r * S.lapse r)) * (1 / r)
      = S.Λ * r ^ 2 / 3 - S.M / r := by
  rw [lapseHalfDeriv_eq]
  field_simp [hf, hr]
  ring

/-- The `r φ r φ` Riemann component for Schwarzschild–de Sitter: `(Λ r² / 3 - M / r) sin²θ`. -/
lemma riemann_r_phirphi (S : SchwarzschildDeSitterSpacetime) (r th : ℝ) (hr : r ≠ 0)
    (hf : S.lapse r ≠ 0) :
    (-(S.lapse r) - r * (2 * S.lapseHalfDeriv r)) * Real.sin th ^ 2
      + (-(S.lapseHalfDeriv r) / S.lapse r) * (-(r * Real.sin th ^ 2 * S.lapse r))
      - (-(r * Real.sin th ^ 2 * S.lapse r)) * (1 / r)
      = (S.Λ * r ^ 2 / 3 - S.M / r) * Real.sin th ^ 2 := by
  rw [lapseHalfDeriv_eq]
  field_simp [hf, hr]
  ring

/-- The `θ φ θ φ` Riemann component for Schwarzschild–de Sitter: `(2M/r + Λr²/3) sin²θ`. -/
lemma riemann_theta_phitheta (S : SchwarzschildDeSitterSpacetime) (r th : ℝ) (hr : r ≠ 0)
    (hsin : Real.sin th ≠ 0) :
    (Real.sin th ^ 2 - Real.cos th ^ 2)
      + (1 / r) * (-(r * Real.sin th ^ 2 * S.lapse r))
      - (-(Real.sin th * Real.cos th)) * (Real.cos th / Real.sin th)
      = (2 * S.M / r + S.Λ * r ^ 2 / 3) * Real.sin th ^ 2 := by
  rw [lapse_eq]
  field_simp [hr, hsin]
  ring

/-- All six independent Schwarzschild–de Sitter Riemann components assembled as one
conjunction. -/
lemma riemann_components (S : SchwarzschildDeSitterSpacetime) (r th : ℝ) (hr : r ≠ 0)
    (hf : S.lapse r ≠ 0) (hsin : Real.sin th ≠ 0) :
    (-(deriv (fun s : ℝ => S.lapseHalfDeriv s / S.lapse s) r)
        + (S.lapseHalfDeriv r / S.lapse r) * (-(S.lapseHalfDeriv r / S.lapse r))
        - (S.lapseHalfDeriv r / S.lapse r) ^ 2
        = (2 * S.M / r ^ 3 + S.Λ / 3) / S.lapse r)
      ∧ ((S.lapseHalfDeriv r / S.lapse r) * (-(r * S.lapse r))
          = S.Λ * r ^ 2 / 3 - S.M / r)
      ∧ ((S.lapseHalfDeriv r / S.lapse r) * (-(r * Real.sin th ^ 2 * S.lapse r))
          = (S.Λ * r ^ 2 / 3 - S.M / r) * Real.sin th ^ 2)
      ∧ ((-(S.lapse r) - r * (2 * S.lapseHalfDeriv r))
            + (-(S.lapseHalfDeriv r) / S.lapse r) * (-(r * S.lapse r))
            - (-(r * S.lapse r)) * (1 / r) = S.Λ * r ^ 2 / 3 - S.M / r)
      ∧ ((-(S.lapse r) - r * (2 * S.lapseHalfDeriv r)) * Real.sin th ^ 2
            + (-(S.lapseHalfDeriv r) / S.lapse r) *
                (-(r * Real.sin th ^ 2 * S.lapse r))
            - (-(r * Real.sin th ^ 2 * S.lapse r)) * (1 / r)
          = (S.Λ * r ^ 2 / 3 - S.M / r) * Real.sin th ^ 2)
      ∧ ((Real.sin th ^ 2 - Real.cos th ^ 2)
            + (1 / r) * (-(r * Real.sin th ^ 2 * S.lapse r))
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

-/

/-- The radial Weyl electric eigenvalue `-f R^t{}_{rtr} + Λ/3 = -2M/r³` is independent of `Λ`. -/
lemma weyl_rr (S : SchwarzschildDeSitterSpacetime) (r : ℝ) (hf : S.lapse r ≠ 0) :
    -(S.lapse r) * ((2 * S.M / r ^ 3 + S.Λ / 3) / S.lapse r) + S.Λ / 3
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
    (hf : S.lapse r ≠ 0) :
    (S.lapse r)⁻¹ * (r ^ 2)⁻¹ * (-(S.lapse r) * (S.Λ * r ^ 2 / 3 - S.M / r))
      + S.Λ / 3 = Schwarzschild.electricPart (S.M / r ^ 3) 2 2 := by
  have h22 : Schwarzschild.electricPart (S.M / r ^ 3) 2 2 = S.M / r ^ 3 := by
    simp [Schwarzschild.electricPart]
  rw [h22]
  field_simp [hr, hf]
  ring

/-- The `φ` Weyl electric eigenvalue equals `M/r³` for every `Λ`. -/
lemma weyl_phiphi (S : SchwarzschildDeSitterSpacetime) (r th : ℝ) (hr : r ≠ 0)
    (hf : S.lapse r ≠ 0) (hsin : Real.sin th ≠ 0) :
    (S.lapse r)⁻¹ * (r ^ 2 * Real.sin th ^ 2)⁻¹
        * (-(S.lapse r) * ((S.Λ * r ^ 2 / 3 - S.M / r) * Real.sin th ^ 2))
      + S.Λ / 3 = Schwarzschild.electricPart (S.M / r ^ 3) 3 3 := by
  have h33 : Schwarzschild.electricPart (S.M / r ^ 3) 3 3 = S.M / r ^ 3 := by
    simp [Schwarzschild.electricPart]
  rw [h33]
  field_simp [hr, hf, hsin]
  ring

end SchwarzschildDeSitterSpacetime

end SchwarzschildDeSitter

end GeneralRelativity
