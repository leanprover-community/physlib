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
eigenvalues directly from the Schwarzschild–de Sitter lapse `f = 1 - 2M/r - Λr²/3`.

## i. Overview

With `f = 1 - 2M/r - Λr²/3` (`sdsF`) and `n = f'/2 = M/r² - Λr/3` (`sdsLapseHalfDeriv`), the mixed
radial Christoffel symbols are `Γ^t_{tr} = n / f` and `Γ^r_{rr} = -n / f`. Differentiating
these expressions yields all six independent Riemann components for general `Λ`:

- `R^t{}_{rtr} = (2M / r³ + Λ / 3) / f`,
- `R^t{}_{θtθ} = R^r{}_{θrθ} = Λ r² / 3 - M / r`,
- `R^t{}_{φtφ} = R^r{}_{φrφ} = (Λ r² / 3 - M / r) sin²θ`,
- `R^θ{}_{φθφ} = (2M / r + Λ r² / 3) sin²θ`.

Lowering into the orthonormal frame and subtracting the trace piece `-(Λ / 3) g` recovers
`electricPart (M / r³)` for every `Λ`: the cosmological constant shifts Ricci curvature while
leaving the Weyl tidal field unchanged.

## ii. Key results

- `SchwarzschildDeSitterSpacetime`, `sdsMetric`, `sdsMetricInv`, `sdsF`, `sdsLapseHalfDeriv` :
  Schwarzschild–de Sitter spacetime structure, coordinate metric, inverse, and lapse.
- `sdsF_zero_lambda` : reduction to `schwarzschildF` at `Λ = 0`.
- `riemann_t_rtr_sds`, `riemann_t_thetatheta_sds`, `riemann_t_phitphi_sds`,
  `riemann_r_thetar_sds`, `riemann_r_phirphi_sds`, `riemann_theta_phitheta_sds` : all six
  Riemann components for general `Λ`.
- `weyl_rr_sds`, `weyl_thetatheta_sds`, `weyl_phiphi_sds` : `Λ`-independence of the Weyl
  electric eigenvalues.

## iii. Table of contents

- A. Lapse function, half-derivative, and Christoffel symbols
- B. The six Riemann components for general `Λ`
- C. `Λ`-independence of the Weyl electric eigenvalues

## iv. References

* R. M. Wald, *General Relativity* (1984). [ref: wald_1984_general_relativity]
* C. W. Misner, K. S. Thorne, and J. A. Wheeler, *Gravitation* (1973). [ref: mtw_1973_gravitation]

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

/-- The Schwarzschild–de Sitter lapse function `f = 1 - 2M / r - Λ r² / 3`. -/
noncomputable def sdsF (M Λ r : ℝ) : ℝ := 1 - 2 * M / r - Λ * r ^ 2 / 3

/-- Half the radial derivative of the lapse, `n = f'/2 = M / r² - Λ r / 3`, factored out so
rational Christoffel and Riemann component expressions avoid repeated factor-of-2 cancellation. -/
noncomputable def sdsLapseHalfDeriv (M Λ r : ℝ) : ℝ := M / r ^ 2 - Λ * r / 3

/-- The Schwarzschild–de Sitter metric in `(t, r, θ, φ)` coordinates. -/
noncomputable def sdsMetric (M Λ : ℝ) (x : Fin 4 → ℝ) : Tensor2 4 :=
  StaticSpherical.staticSphericalMetric (sdsF M Λ) x

/-- The inverse of the Schwarzschild–de Sitter metric in `(t, r, θ, φ)` coordinates. -/
noncomputable def sdsMetricInv (M Λ : ℝ) (x : Fin 4 → ℝ) : Tensor2 4 :=
  StaticSpherical.staticSphericalMetricInv (sdsF M Λ) x

/-- At `Λ = 0`, the de Sitter lapse reduces to the Schwarzschild lapse. -/
lemma sdsF_zero_lambda (M r : ℝ) : sdsF M 0 r = Schwarzschild.schwarzschildF M r := by
  simp [sdsF, Schwarzschild.schwarzschildF]

/-- `f = 1 - 2M/r - Λr²/3` is differentiable away from `r = 0` with `f' = 2 n`. -/
lemma hasDerivAt_sdsF (M Λ r : ℝ) (hr : r ≠ 0) :
    HasDerivAt (fun s : ℝ => sdsF M Λ s) (2 * sdsLapseHalfDeriv M Λ r) r := by
  have h1 : HasDerivAt (fun s : ℝ => 1 - 2 * M / s) (2 * M / r ^ 2) r :=
    Schwarzschild.hasDerivAt_gtt M r hr
  have h2 : HasDerivAt (fun s : ℝ => Λ / 3 * s ^ 2) (Λ / 3 * (2 * r)) r := by
    have h := (hasDerivAt_pow 2 r).const_mul (Λ / 3)
    simpa using h
  have h := h1.sub h2
  have hfun : (fun s : ℝ => sdsF M Λ s)
      = (fun s : ℝ => 1 - 2 * M / s) - fun s : ℝ => Λ / 3 * s ^ 2 := by
    funext s
    simp [sdsF, Pi.sub_apply]
    ring
  have hval : 2 * M / r ^ 2 - Λ / 3 * (2 * r) = 2 * sdsLapseHalfDeriv M Λ r := by
    simp [sdsLapseHalfDeriv]
    ring
  rw [← hfun, hval] at h
  exact h

/-- `f' = 2 n` as an identity for `deriv`. -/
lemma deriv_sdsF (M Λ r : ℝ) (hr : r ≠ 0) :
    deriv (fun s : ℝ => sdsF M Λ s) r = 2 * sdsLapseHalfDeriv M Λ r :=
  (hasDerivAt_sdsF M Λ r hr).deriv

/-- `n = M/r² - Λr/3` is differentiable away from `r = 0` with `n' = -2M/r³ - Λ/3`. -/
lemma hasDerivAt_sdsLapseHalfDeriv (M Λ r : ℝ) (hr : r ≠ 0) :
    HasDerivAt (fun s : ℝ => sdsLapseHalfDeriv M Λ s) (-2 * M / r ^ 3 - Λ / 3) r := by
  have h1 : HasDerivAt (fun s : ℝ => M / s ^ 2) (-2 * M / r ^ 3) r :=
    Schwarzschild.potential_second_hasDerivAt M r hr
  have h2 : HasDerivAt (fun s : ℝ => Λ / 3 * s) (Λ / 3) r := by
    simpa using (hasDerivAt_id r).const_mul (Λ / 3)
  have h := h1.sub h2
  have hfun : (fun s : ℝ => sdsLapseHalfDeriv M Λ s)
      = (fun s : ℝ => M / s ^ 2) - fun s : ℝ => Λ / 3 * s := by
    funext s
    simp [sdsLapseHalfDeriv, Pi.sub_apply]
    ring
  rw [← hfun] at h
  exact h

/-- `n' = -2M/r³ - Λ/3` as an identity for `deriv`. -/
lemma deriv_sdsLapseHalfDeriv (M Λ r : ℝ) (hr : r ≠ 0) :
    deriv (fun s : ℝ => sdsLapseHalfDeriv M Λ s) r = -2 * M / r ^ 3 - Λ / 3 :=
  (hasDerivAt_sdsLapseHalfDeriv M Λ r hr).deriv

/-- `Γ^t_{tr} = (1/2) g^{tt} ∂_r g_{tt} = n / f`. -/
lemma gammaTtr_sds (M Λ r : ℝ) (hf : sdsF M Λ r ≠ 0) :
    (1 / 2 : ℝ) * (-(sdsF M Λ r)⁻¹) * (-(2 * sdsLapseHalfDeriv M Λ r))
      = sdsLapseHalfDeriv M Λ r / sdsF M Λ r := by
  field_simp [hf]

/-- `∂_r (f⁻¹) = -2 n / f²`. -/
lemma deriv_sdsF_inv (M Λ r : ℝ) (hr : r ≠ 0) (hf : sdsF M Λ r ≠ 0) :
    deriv (fun s : ℝ => (sdsF M Λ s)⁻¹) r
      = -(2 * sdsLapseHalfDeriv M Λ r) / (sdsF M Λ r) ^ 2 :=
  (hasDerivAt_sdsF M Λ r hr).inv hf |>.deriv

/-- `Γ^r_{rr} = (1/2) g^{rr} ∂_r g_{rr} = -n / f`. -/
lemma gammaRrr_sds (M Λ r : ℝ) (hr : r ≠ 0) (hf : sdsF M Λ r ≠ 0) :
    (1 / 2 : ℝ) * (sdsF M Λ r) * deriv (fun s : ℝ => (sdsF M Λ s)⁻¹) r
      = -sdsLapseHalfDeriv M Λ r / sdsF M Λ r := by
  rw [deriv_sdsF_inv M Λ r hr hf]
  field_simp [hf]

/-- `Γ^r_{θθ} = -r f`. -/
lemma gammaRthth_sds (M Λ r : ℝ) :
    (1 / 2 : ℝ) * (sdsF M Λ r) * (-(2 * r)) = -(r * sdsF M Λ r) := by
  ring

/-- `Γ^r_{φφ} = -r f sin²θ`. -/
lemma gammaRphiphi_sds (M Λ r th : ℝ) :
    (1 / 2 : ℝ) * (sdsF M Λ r) * (-(2 * r * Real.sin th ^ 2))
      = -(r * Real.sin th ^ 2 * sdsF M Λ r) := by
  ring

/-!

## B. The six Riemann components for general `Λ`

-/

/-- Equational form of `sdsF M Λ r`. -/
lemma sdsF_eq (M Λ r : ℝ) : sdsF M Λ r = 1 - 2 * M / r - Λ * r ^ 2 / 3 := rfl

/-- Equational form of `sdsLapseHalfDeriv M Λ r`. -/
lemma sdsLapseHalfDeriv_eq (M Λ r : ℝ) :
    sdsLapseHalfDeriv M Λ r = M / r ^ 2 - Λ * r / 3 := rfl

/-- The `t r t r` Riemann component for Schwarzschild–de Sitter: `(2M/r³ + Λ/3)/f`. -/
lemma riemann_t_rtr_sds (M Λ r : ℝ) (hr : r ≠ 0) (hf : sdsF M Λ r ≠ 0) :
    -(deriv (fun s : ℝ => sdsLapseHalfDeriv M Λ s / sdsF M Λ s) r)
      + (sdsLapseHalfDeriv M Λ r / sdsF M Λ r) * (-(sdsLapseHalfDeriv M Λ r / sdsF M Λ r))
      - (sdsLapseHalfDeriv M Λ r / sdsF M Λ r) ^ 2
      = (2 * M / r ^ 3 + Λ / 3) / sdsF M Λ r := by
  have hq : deriv (fun s : ℝ => sdsLapseHalfDeriv M Λ s / sdsF M Λ s) r
      = (-2 * M / r ^ 3 - Λ / 3) / sdsF M Λ r
          - sdsLapseHalfDeriv M Λ r * (2 * sdsLapseHalfDeriv M Λ r) / (sdsF M Λ r) ^ 2 := by
    have h := (hasDerivAt_sdsLapseHalfDeriv M Λ r hr).div (hasDerivAt_sdsF M Λ r hr) hf
    have hfun : (fun s : ℝ => sdsLapseHalfDeriv M Λ s / sdsF M Λ s)
        = (fun s : ℝ => sdsLapseHalfDeriv M Λ s) / fun s : ℝ => sdsF M Λ s := rfl
    rw [hfun, h.deriv]
    field_simp [hf]
  rw [hq]
  field_simp [hf, hr]
  ring

/-- The `t θ t θ` Riemann component for Schwarzschild–de Sitter: `Λ r² / 3 - M / r`. -/
lemma riemann_t_thetatheta_sds (M Λ r : ℝ) (hr : r ≠ 0) (hf : sdsF M Λ r ≠ 0) :
    (sdsLapseHalfDeriv M Λ r / sdsF M Λ r) * (-(r * sdsF M Λ r))
      = Λ * r ^ 2 / 3 - M / r := by
  rw [sdsLapseHalfDeriv_eq]
  field_simp [hf, hr]
  ring

/-- The `t φ t φ` Riemann component for Schwarzschild–de Sitter: `(Λ r² / 3 - M / r) sin²θ`. -/
lemma riemann_t_phitphi_sds (M Λ r th : ℝ) (hr : r ≠ 0)
    (hf : sdsF M Λ r ≠ 0) :
    (sdsLapseHalfDeriv M Λ r / sdsF M Λ r) * (-(r * Real.sin th ^ 2 * sdsF M Λ r))
      = (Λ * r ^ 2 / 3 - M / r) * Real.sin th ^ 2 := by
  rw [sdsLapseHalfDeriv_eq]
  field_simp [hf, hr]
  ring

/-- The `r θ r θ` Riemann component for Schwarzschild–de Sitter: `Λ r² / 3 - M / r`. -/
lemma riemann_r_thetar_sds (M Λ r : ℝ) (hr : r ≠ 0) (hf : sdsF M Λ r ≠ 0) :
    (-(sdsF M Λ r) - r * (2 * sdsLapseHalfDeriv M Λ r))
      + (-(sdsLapseHalfDeriv M Λ r) / sdsF M Λ r) * (-(r * sdsF M Λ r))
      - (-(r * sdsF M Λ r)) * (1 / r)
      = Λ * r ^ 2 / 3 - M / r := by
  rw [sdsLapseHalfDeriv_eq]
  field_simp [hf, hr]
  ring

/-- The `r φ r φ` Riemann component for Schwarzschild–de Sitter: `(Λ r² / 3 - M / r) sin²θ`. -/
lemma riemann_r_phirphi_sds (M Λ r th : ℝ) (hr : r ≠ 0)
    (hf : sdsF M Λ r ≠ 0) :
    (-(sdsF M Λ r) - r * (2 * sdsLapseHalfDeriv M Λ r)) * Real.sin th ^ 2
      + (-(sdsLapseHalfDeriv M Λ r) / sdsF M Λ r) * (-(r * Real.sin th ^ 2 * sdsF M Λ r))
      - (-(r * Real.sin th ^ 2 * sdsF M Λ r)) * (1 / r)
      = (Λ * r ^ 2 / 3 - M / r) * Real.sin th ^ 2 := by
  rw [sdsLapseHalfDeriv_eq]
  field_simp [hf, hr]
  ring

/-- The `θ φ θ φ` Riemann component for Schwarzschild–de Sitter: `(2M/r + Λr²/3) sin²θ`. -/
lemma riemann_theta_phitheta_sds (M Λ r th : ℝ) (hr : r ≠ 0)
    (hsin : Real.sin th ≠ 0) :
    (Real.sin th ^ 2 - Real.cos th ^ 2)
      + (1 / r) * (-(r * Real.sin th ^ 2 * sdsF M Λ r))
      - (-(Real.sin th * Real.cos th)) * (Real.cos th / Real.sin th)
      = (2 * M / r + Λ * r ^ 2 / 3) * Real.sin th ^ 2 := by
  rw [sdsF_eq]
  field_simp [hr, hsin]
  ring

/-- All six independent Schwarzschild–de Sitter Riemann components assembled as one
conjunction. -/
lemma riemann_components_sds (M Λ r th : ℝ) (hr : r ≠ 0)
    (hf : sdsF M Λ r ≠ 0) (hsin : Real.sin th ≠ 0) :
    (-(deriv (fun s : ℝ => sdsLapseHalfDeriv M Λ s / sdsF M Λ s) r)
        + (sdsLapseHalfDeriv M Λ r / sdsF M Λ r) * (-(sdsLapseHalfDeriv M Λ r / sdsF M Λ r))
        - (sdsLapseHalfDeriv M Λ r / sdsF M Λ r) ^ 2
        = (2 * M / r ^ 3 + Λ / 3) / sdsF M Λ r)
      ∧ ((sdsLapseHalfDeriv M Λ r / sdsF M Λ r) * (-(r * sdsF M Λ r))
          = Λ * r ^ 2 / 3 - M / r)
      ∧ ((sdsLapseHalfDeriv M Λ r / sdsF M Λ r) * (-(r * Real.sin th ^ 2 * sdsF M Λ r))
          = (Λ * r ^ 2 / 3 - M / r) * Real.sin th ^ 2)
      ∧ ((-(sdsF M Λ r) - r * (2 * sdsLapseHalfDeriv M Λ r))
            + (-(sdsLapseHalfDeriv M Λ r) / sdsF M Λ r) * (-(r * sdsF M Λ r))
            - (-(r * sdsF M Λ r)) * (1 / r) = Λ * r ^ 2 / 3 - M / r)
      ∧ ((-(sdsF M Λ r) - r * (2 * sdsLapseHalfDeriv M Λ r)) * Real.sin th ^ 2
            + (-(sdsLapseHalfDeriv M Λ r) / sdsF M Λ r) * (-(r * Real.sin th ^ 2 * sdsF M Λ r))
            - (-(r * Real.sin th ^ 2 * sdsF M Λ r)) * (1 / r)
          = (Λ * r ^ 2 / 3 - M / r) * Real.sin th ^ 2)
      ∧ ((Real.sin th ^ 2 - Real.cos th ^ 2)
            + (1 / r) * (-(r * Real.sin th ^ 2 * sdsF M Λ r))
            - (-(Real.sin th * Real.cos th)) * (Real.cos th / Real.sin th)
          = (2 * M / r + Λ * r ^ 2 / 3) * Real.sin th ^ 2) :=
  ⟨riemann_t_rtr_sds M Λ r hr hf,
   riemann_t_thetatheta_sds M Λ r hr hf,
   riemann_t_phitphi_sds M Λ r th hr hf,
   riemann_r_thetar_sds M Λ r hr hf,
   riemann_r_phirphi_sds M Λ r th hr hf,
   riemann_theta_phitheta_sds M Λ r th hr hsin⟩

/-!

## C. `Λ`-independence of the Weyl electric eigenvalues

-/

/-- The radial Weyl electric eigenvalue `-f R^t{}_{rtr} + Λ/3 = -2M/r³` is independent of `Λ`. -/
lemma weyl_rr_sds (M Λ r : ℝ) (hf : sdsF M Λ r ≠ 0) :
    -(sdsF M Λ r) * ((2 * M / r ^ 3 + Λ / 3) / sdsF M Λ r) + Λ / 3
      = Schwarzschild.electricPart (M / r ^ 3) 1 1 := by
  have h11 : Schwarzschild.electricPart (M / r ^ 3) 1 1 = -(2 * M / r ^ 3) := by
    simp [Schwarzschild.electricPart]
    ring
  rw [h11]
  field_simp [hf]
  ring

/-- The `θ` Weyl electric eigenvalue `f⁻¹ r⁻² (-f) (Λr²/3 - M/r) + Λ/3 = M/r³` is independent
of `Λ`. -/
lemma weyl_thetatheta_sds (M Λ r : ℝ) (hr : r ≠ 0) (hf : sdsF M Λ r ≠ 0) :
    (sdsF M Λ r)⁻¹ * (r ^ 2)⁻¹ * (-(sdsF M Λ r) * (Λ * r ^ 2 / 3 - M / r))
      + Λ / 3 = Schwarzschild.electricPart (M / r ^ 3) 2 2 := by
  have h22 : Schwarzschild.electricPart (M / r ^ 3) 2 2 = M / r ^ 3 := by
    simp [Schwarzschild.electricPart]
  rw [h22]
  field_simp [hr, hf]
  ring

/-- The `φ` Weyl electric eigenvalue equals `M/r³` for every `Λ`. -/
lemma weyl_phiphi_sds (M Λ r th : ℝ) (hr : r ≠ 0) (hf : sdsF M Λ r ≠ 0)
    (hsin : Real.sin th ≠ 0) :
    (sdsF M Λ r)⁻¹ * (r ^ 2 * Real.sin th ^ 2)⁻¹
        * (-(sdsF M Λ r) * ((Λ * r ^ 2 / 3 - M / r) * Real.sin th ^ 2))
      + Λ / 3 = Schwarzschild.electricPart (M / r ^ 3) 3 3 := by
  have h33 : Schwarzschild.electricPart (M / r ^ 3) 3 3 = M / r ^ 3 := by
    simp [Schwarzschild.electricPart]
  rw [h33]
  field_simp [hr, hf, hsin]
  ring

/-- The lapse function `f(r) = 1 - 2M / r - Λ r² / 3` of a Schwarzschild–de Sitter spacetime. -/
noncomputable def SchwarzschildDeSitterSpacetime.lapse (S : SchwarzschildDeSitterSpacetime)
    (r : ℝ) : ℝ :=
  sdsF S.M S.Λ r

/-- The coordinate metric of a Schwarzschild–de Sitter spacetime. -/
noncomputable def SchwarzschildDeSitterSpacetime.metric (S : SchwarzschildDeSitterSpacetime)
    (x : Fin 4 → ℝ) : Tensor2 4 :=
  sdsMetric S.M S.Λ x

/-- The inverse coordinate metric of a Schwarzschild–de Sitter spacetime. -/
noncomputable def SchwarzschildDeSitterSpacetime.metricInv (S : SchwarzschildDeSitterSpacetime)
    (x : Fin 4 → ℝ) : Tensor2 4 :=
  sdsMetricInv S.M S.Λ x

end SchwarzschildDeSitter

end GeneralRelativity
