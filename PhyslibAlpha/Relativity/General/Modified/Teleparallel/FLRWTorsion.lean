/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import Mathlib.LinearAlgebra.Matrix.Notation
public import PhyslibAlpha.Cosmology.FLRW.Metric
public import PhyslibAlpha.Relativity.General.Modified.Teleparallel.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!

# Flat FLRW teleparallel torsion and the boundary equivalence `R_LC = -T + B`

Diagonal comoving flat FLRW tetrad, Weitzenböck Hubble connection, torsion scalar `T = 6 H²`,
and exact equivalence `ricciScalarOf = -T + B` with `FLRW.ricciScalarOf_flrw`.

## i. Overview

On a spatially flat FLRW cosmology with diagonal tetrad `e^A_i = diag(1, a(t), a(t), a(t))`, the
teleparallel torsion scalar reduces to `T = 6 H² = 6 (a'/a)²`, and the Levi-Civita Ricci scalar
computed by the metric pipeline satisfies `R_LC = -T + B`.

## ii. Key results

- `flrwTetrad`, `flrwTetradInv`, `flrwTetrad_mul_inv` : diagonal flat FLRW comoving tetrad.
- `flrwWeitzenbock_hubble` : spatial Weitzenböck connection equals Hubble parameter `a'/a`.
- `flrwTorsionScalar`, `flrwBoundaryTerm`, `ricciScalarOf_flrw_flat_eq_neg_torsion_add_boundary` :
  exact equivalence `R_LC = -T + B` bridged to `FLRW.ricciScalarOf_flrw`.

## iii. Table of contents

- A. Flat FLRW teleparallel cosmology and `R_LC = -T + B`

## iv. References

* Albert Einstein, *Riemann-Geometrie mit Aufrechterhaltung des Begriffes des Fernparallelismus*,
  *Sitzungsberichte der Preussischen Akademie der Wissenschaften, Physikalisch-Mathematische
  Klasse* (1928). [ref: Einstein1928]
* Kenji Hayashi and Takeshi Shirafuji, *New General Relativity*, *Physical Review D* (1979). [ref:
  HayashiShirafuji1979]
* José W. Maluf, *The Teleparallel Equivalent of General Relativity*, *Annalen der Physik* (2013)
  (https://arxiv.org/abs/1303.3897). [ref: Maluf2013]
* Martin Krššák and Emmanuel N. Saridakis, *The Covariant Formulation of $f(T)$ Gravity*,
  *Classical and Quantum Gravity* (2016) (https://arxiv.org/abs/1510.08432). [ref:
  KrssakSaridakis2016]

-/

@[expose] public section

namespace GeneralRelativity

namespace Modified

namespace Teleparallel

open GeneralRelativity.Pipeline
open GeneralRelativity.FLRW

/-!

## A. Flat FLRW teleparallel cosmology and `R_LC = -T + B`

-/

/-- Diagonal flat FLRW comoving tetrad `e^A_i = diag(1, a(t), a(t), a(t))`. -/
def flrwTetrad (a : ℝ → ℝ) (x : Fin 4 → ℝ) : Tensor2 4 :=
  Matrix.diagonal ![1, a (x 0), a (x 0), a (x 0)]

/-- Inverse of the diagonal flat FLRW comoving tetrad:
`e_A^i = diag(1, a(t)⁻¹, a(t)⁻¹, a(t)⁻¹)`. -/
noncomputable def flrwTetradInv (a : ℝ → ℝ) (x : Fin 4 → ℝ) : Tensor2 4 :=
  Matrix.diagonal ![1, (a (x 0))⁻¹, (a (x 0))⁻¹, (a (x 0))⁻¹]

/-- Orthonormality of the flat FLRW tetrad: `flrwTetrad * flrwTetradInv = 1` when `a(t) ≠ 0`. -/
lemma flrwTetrad_mul_inv (a : ℝ → ℝ) (x : Fin 4 → ℝ) (ha : a (x 0) ≠ 0) :
    flrwTetrad a x * flrwTetradInv a x = 1 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply]
  fin_cases i <;> fin_cases j <;>
    simp [flrwTetrad, flrwTetradInv, Fin.sum_univ_four, ha]

/-- Spatial Weitzenböck connection component `Γ^k_{0k} = H = a'(t) / a(t)` for `k ∈ {1, 2, 3}` on
a flat FLRW background. -/
lemma flrwWeitzenbock_hubble (a : ℝ → ℝ) (x : Fin 4 → ℝ) (k : Fin 4) (hk : k ≠ 0) :
    flrwTetradInv a x k k * coordDeriv 0 (fun y => flrwTetrad a y k k) x =
      deriv a (x 0) / a (x 0) := by
  have hfun : (fun s => flrwTetrad a (Function.update x 0 s) k k) = a := by
    funext s
    fin_cases k
    · exact False.elim (hk rfl)
    · simp [flrwTetrad]
    · simp [flrwTetrad]
    · simp [flrwTetrad]
  have hinv : flrwTetradInv a x k k = (a (x 0))⁻¹ := by
    fin_cases k
    · exact False.elim (hk rfl)
    · simp [flrwTetradInv]
    · simp [flrwTetradInv]
    · simp [flrwTetradInv]
  rw [coordDeriv, hfun, hinv, div_eq_inv_mul]

/-- Flat FLRW teleparallel torsion scalar `T = 6 H² = 6 (a'(t) / a(t))²`. -/
noncomputable def flrwTorsionScalar (a : ℝ → ℝ) (t : ℝ) : ℝ :=
  6 * (deriv a t / a t) ^ 2

/-- Flat FLRW teleparallel total-divergence boundary term
`B = (2 / a³) ∂_t (3 a² a') = 6 (a'' / a + 2 (a' / a)²)`. -/
noncomputable def flrwBoundaryTerm (a : ℝ → ℝ) (t : ℝ) : ℝ :=
  6 * (deriv (deriv a) t / a t + 2 * (deriv a t / a t) ^ 2)

/-- Exact teleparallel-to-Levi-Civita scalar curvature equivalence on flat FLRW spacetime (`k = 0`):
`ricciScalarOf (flrwMetric a 0) (flrwMetricInv a 0) x = -T + B`. -/
lemma ricciScalarOf_flrw_flat_eq_neg_torsion_add_boundary (a : ℝ → ℝ) (x : Fin 4 → ℝ)
    (ha : a (x 0) ≠ 0) (hr : x 1 ≠ 0) (hsin : Real.sin (x 2) ≠ 0)
    (ha_diff : ∀ᶠ t in nhds (x 0), DifferentiableAt ℝ a t)
    (ha2 : DifferentiableAt ℝ (deriv a) (x 0)) :
    ricciScalarOf (flrwMetric a 0) (flrwMetricInv a 0) x =
      -flrwTorsionScalar a (x 0) + flrwBoundaryTerm a (x 0) := by
  have hkr : 1 - 0 * (x 1) ^ 2 ≠ 0 := by norm_num
  rw [ricciScalarOf_flrw a 0 x ha hr hkr hsin ha_diff ha2]
  simp only [flrwTorsionScalar, flrwBoundaryTerm]
  ring

/-- For a Physlib `Cosmology.FLRW` universe, `flrwTorsionScalar` reproduces `6 H²` in terms of
`Cosmology.FLRW.FriedmannEquation.hubbleConstant`. -/
lemma flrwTorsionScalar_ofCosmology (U : Cosmology.FLRW) {t : Time} (ht : t ∈ U.I) :
    flrwTorsionScalar (flrwScaleFn U) t.val =
      6 * (Cosmology.FLRW.FriedmannEquation.hubbleConstant U.a t) ^ 2 := by
  simp only [flrwTorsionScalar, deriv_flrwScaleFn_eq U ht,
    Cosmology.FLRW.FriedmannEquation.hubbleConstant]
  rfl

end Teleparallel

end Modified

end GeneralRelativity
