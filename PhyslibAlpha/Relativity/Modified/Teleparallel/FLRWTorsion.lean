/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import Mathlib.LinearAlgebra.Matrix.Notation
public import PhyslibAlpha.Cosmology.FLRW.FriedmannEquations
public import PhyslibAlpha.Relativity.Modified.Teleparallel.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!

# Flat FLRW teleparallel torsion and the boundary equivalence `R_LC = -T + B`

Diagonal comoving flat FLRW tetrad, Weitzenböck Hubble connection, torsion scalar `T = 6 H²`,
and exact equivalence `R_LC = -T + B` with `FLRWSpacetime.ricciScalar`.

## i. Overview

On a spatially flat FLRW cosmology with diagonal tetrad `e^A_i = diag(1, a(t), a(t), a(t))`, the
teleparallel torsion scalar reduces to `T = 6 H² = 6 (a'/a)²`, and the Levi-Civita Ricci scalar
computed from the coordinate metric satisfies `R_LC = -T + B`.

## ii. Key results

- `flrwTetrad`, `flrwTetradInv`, `flrwTetrad_mul_inv`, `flrwTetradFrame` : diagonal flat FLRW
  comoving tetrad and `Tetrad 4` structure.
- `flrwWeitzenbock_hubble` : spatial Weitzenböck connection equals Hubble parameter `a'/a`.
- `flrwTorsionScalar`, `torsionScalar_flrw_eq_flrwTorsionScalar`, `flrwBoundaryTerm`,
  `ricciScalar_flrw_flat_eq_neg_torsion_add_boundary` : reconciliation of `torsionScalar` with
  `flrwTorsionScalar = 6 H²` and exact equivalence `R_LC = -T + B` bridged to
  `FLRWSpacetime.ricciScalar`.

## iii. Table of contents

- A. Flat FLRW teleparallel cosmology and `R_LC = -T + B`

## iv. References

* Albert Einstein, *Riemann-Geometrie mit Aufrechterhaltung des Begriffes des Fernparallelismus*,
  *Sitzungsberichte der Preussischen Akademie der Wissenschaften, Physikalisch-Mathematische Klasse*
  (1928), pp. 217-221. [ref: Einstein1928]
* Kenji Hayashi and Takeshi Shirafuji, *New General Relativity*, *Physical Review D* 19, pp.
  3524-3553 (1979), Sec. II. [ref: HayashiShirafuji1979]
* José W. Maluf, *The Teleparallel Equivalent of General Relativity*, *Annalen der Physik* (2013),
  Sec. 2-3 (https://arxiv.org/pdf/1303.3897#page=3). [ref: Maluf2013]
* Martin Krššák and Emmanuel N. Saridakis, *The Covariant Formulation of $f(T)$ Gravity*, *Classical
  and Quantum Gravity* (2016), Sec. 3 (https://arxiv.org/pdf/1510.08432#page=6).
  [ref: KrssakSaridakis2016]
-/

@[expose] public section

namespace GeneralRelativity

namespace Modified

namespace Teleparallel

open GeneralRelativity.CoordinateCurvature
open Cosmology.FLRW
open GeneralRelativity.Modified.EinsteinCartan

/-!

## A. Flat FLRW teleparallel cosmology and `R_LC = -T + B`

Instantiating the diagonal flat FLRW comoving tetrad yields the Hubble connection, `T = 6 H²`,
and exact agreement with `FLRWSpacetime.ricciScalar` up to the boundary divergence `B`.

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

/-- Inverse-to-coframe orthonormality of the flat FLRW tetrad:
`flrwTetradInv * flrwTetrad = 1` when `a(t) ≠ 0`. -/
lemma flrwTetradInv_mul (a : ℝ → ℝ) (x : Fin 4 → ℝ) (ha : a (x 0) ≠ 0) :
    flrwTetradInv a x * flrwTetrad a x = 1 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply]
  fin_cases i <;> fin_cases j <;>
    simp [flrwTetrad, flrwTetradInv, Fin.sum_univ_four, ha]

/-- The diagonal flat FLRW comoving frame as a `Tetrad 4` when `a(t) ≠ 0`. -/
noncomputable def flrwTetradFrame (a : ℝ → ℝ) (x : Fin 4 → ℝ) (ha : a (x 0) ≠ 0) : Tetrad 4 where
  e := flrwTetrad a x
  einv := flrwTetradInv a x
  inv_left := flrwTetrad_mul_inv a x ha
  inv_right := flrwTetradInv_mul a x ha

/-- Coordinate partial derivatives `∂_u e^A_j` of the flat FLRW comoving tetrad `flrwTetrad`. -/
noncomputable def flrwTetradDeriv (a : ℝ → ℝ) (x : Fin 4 → ℝ) : Fin 4 → Tensor2 4 :=
  fun u => Matrix.of fun A j => coordDeriv u (fun y => flrwTetrad a y A j) x

/-- Spatial Weitzenböck connection component `Γ^k_{0k} = H = a'(t) / a(t)` for `k ∈ {1, 2, 3}` on
a flat FLRW background, computed from `flrwTetradFrame.weitzenbockConnection`. -/
lemma flrwWeitzenbock_hubble (a : ℝ → ℝ) (x : Fin 4 → ℝ) (ha : a (x 0) ≠ 0) (k : Fin 4)
    (hk : k ≠ 0) :
    (flrwTetradFrame a x ha).weitzenbockConnection (flrwTetradDeriv a x) k 0 k =
      deriv a (x 0) / a (x 0) := by
  have hfun : (fun s => flrwTetrad a (Function.update x 0 s) k k) = a := by
    funext s
    fin_cases k
    · exact False.elim (hk rfl)
    · simp [flrwTetrad]
    · simp [flrwTetrad]
    · simp [flrwTetrad]
  have hdiag : ∀ A : Fin 4, flrwTetradInv a x k A =
      if k = A then ![(1 : ℝ), (a (x 0))⁻¹, (a (x 0))⁻¹, (a (x 0))⁻¹] k else 0 := by
    intro A
    simp [flrwTetradInv, Matrix.diagonal_apply]
  simp only [Tetrad.weitzenbockConnection, flrwTetradFrame, flrwTetradDeriv, Matrix.of_apply,
    hdiag, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  rw [coordDeriv, hfun, div_eq_inv_mul]
  fin_cases k
  · exact False.elim (hk rfl)
  · simp
  · simp
  · simp

/-- Flat FLRW teleparallel torsion scalar `T = 6 H² = 6 (a'(t) / a(t))²`. -/
noncomputable def flrwTorsionScalar (a : ℝ → ℝ) (t : ℝ) : ℝ :=
  6 * (deriv a t / a t) ^ 2

/-- Flat FLRW teleparallel total-divergence boundary term
`B = (2 / a³) ∂_t (3 a² a') = 6 (a'' / a + 2 (a' / a)²)`. -/
noncomputable def flrwBoundaryTerm (a : ℝ → ℝ) (t : ℝ) : ℝ :=
  6 * (deriv (deriv a) t / a t + 2 * (deriv a t / a t) ^ 2)

/-- The inverse diagonal of the Cartesian flat FLRW metric is a left inverse when `a(t) ≠ 0`. -/
lemma flrwCartesianMetricInv_mul (a : ℝ → ℝ) (x : Fin 4 → ℝ) (ha : a (x 0) ≠ 0) :
    Matrix.diagonal ![-1, (a (x 0) ^ 2)⁻¹, (a (x 0) ^ 2)⁻¹, (a (x 0) ^ 2)⁻¹] *
      Matrix.diagonal ![-1, a (x 0) ^ 2, a (x 0) ^ 2, a (x 0) ^ 2] = 1 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply]
  fin_cases i <;> fin_cases j <;> simp [Fin.sum_univ_four, ha]

/-- Cartesian flat FLRW metric `diag(-1, a², a², a²)` induced by the comoving tetrad `flrwTetrad`
when `a(t) ≠ 0`. -/
noncomputable def flrwCartesianMetricTensor (a : ℝ → ℝ) (x : Fin 4 → ℝ) (ha : a (x 0) ≠ 0) :
    MetricTensor 4 where
  g := Matrix.diagonal ![-1, a (x 0) ^ 2, a (x 0) ^ 2, a (x 0) ^ 2]
  ginv := Matrix.diagonal ![-1, (a (x 0) ^ 2)⁻¹, (a (x 0) ^ 2)⁻¹, (a (x 0) ^ 2)⁻¹]
  symm := Matrix.isSymm_diagonal _
  inv_left := mul_eq_one_of_isSymm_of_mul_eq_one (Matrix.isSymm_diagonal _)
    (flrwCartesianMetricInv_mul a x ha)
  inv_right := flrwCartesianMetricInv_mul a x ha

private lemma flrwTetrad_coordDeriv_eq (a : ℝ → ℝ) (x : Fin 4 → ℝ) (u A j : Fin 4) :
    flrwTetradDeriv a x u A j =
      if u = 0 ∧ A = j ∧ j ≠ 0 then deriv a (x 0) else 0 := by
  simp only [flrwTetradDeriv, Matrix.of_apply]
  by_cases hu : u = 0
  · subst hu
    have hfun : ∀ k : Fin 4, k ≠ 0 →
        (fun s => flrwTetrad a (Function.update x 0 s) k k) = a := by
      intro k hk
      funext s
      fin_cases k
      · exact False.elim (hk rfl)
      · simp [flrwTetrad]
      · simp [flrwTetrad]
      · simp [flrwTetrad]
    fin_cases A <;> fin_cases j <;> simp [flrwTetrad, coordDeriv]
  · have hconst : ∀ s, flrwTetrad a (Function.update x u s) A j = flrwTetrad a x A j := by
      intro s
      have h0 : Function.update x u s 0 = x 0 := Function.update_of_ne (Ne.symm hu) s x
      simp [flrwTetrad, h0]
    simp [hu]
    exact coordDeriv_const_slice u (f := fun y => flrwTetrad a y A j) _ hconst

private lemma flrwTetradFrame_weitzenbockTorsion_eq_k0 (a : ℝ → ℝ) (x : Fin 4 → ℝ)
    (ha : a (x 0) ≠ 0) (i j : Fin 4) :
    (flrwTetradFrame a x ha).weitzenbockTorsion (flrwTetradDeriv a x) 0 i j =
      if (0 : Fin 4) ≠ 0 ∧ i = 0 ∧ j = 0 then deriv a (x 0) / a (x 0)
      else if (0 : Fin 4) ≠ 0 ∧ j = 0 ∧ i = 0 then -(deriv a (x 0) / a (x 0))
      else 0 := by
  have hdiag : ∀ A : Fin 4, flrwTetradInv a x 0 A =
      if (0 : Fin 4) = A then ![(1 : ℝ), (a (x 0))⁻¹, (a (x 0))⁻¹, (a (x 0))⁻¹] 0 else 0 := by
    intro A
    simp [flrwTetradInv, Matrix.diagonal_apply]
  rw [Tetrad.weitzenbockTorsion_eq]
  simp only [flrwTetradFrame, hdiag, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
    ↓reduceIte, flrwTetrad_coordDeriv_eq]
  fin_cases i <;> fin_cases j <;> simp [div_eq_inv_mul]

private lemma flrwTetradFrame_weitzenbockTorsion_eq_k1 (a : ℝ → ℝ) (x : Fin 4 → ℝ)
    (ha : a (x 0) ≠ 0) (i j : Fin 4) :
    (flrwTetradFrame a x ha).weitzenbockTorsion (flrwTetradDeriv a x) 1 i j =
      if (1 : Fin 4) ≠ 0 ∧ i = 0 ∧ j = 1 then deriv a (x 0) / a (x 0)
      else if (1 : Fin 4) ≠ 0 ∧ j = 0 ∧ i = 1 then -(deriv a (x 0) / a (x 0))
      else 0 := by
  have hdiag : ∀ A : Fin 4, flrwTetradInv a x 1 A =
      if (1 : Fin 4) = A then ![(1 : ℝ), (a (x 0))⁻¹, (a (x 0))⁻¹, (a (x 0))⁻¹] 1 else 0 := by
    intro A
    simp [flrwTetradInv, Matrix.diagonal_apply]
  rw [Tetrad.weitzenbockTorsion_eq]
  simp only [flrwTetradFrame, hdiag, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
    ↓reduceIte, flrwTetrad_coordDeriv_eq]
  fin_cases i <;> fin_cases j <;> simp [div_eq_inv_mul]

private lemma flrwTetradFrame_weitzenbockTorsion_eq_k2 (a : ℝ → ℝ) (x : Fin 4 → ℝ)
    (ha : a (x 0) ≠ 0) (i j : Fin 4) :
    (flrwTetradFrame a x ha).weitzenbockTorsion (flrwTetradDeriv a x) 2 i j =
      if (2 : Fin 4) ≠ 0 ∧ i = 0 ∧ j = 2 then deriv a (x 0) / a (x 0)
      else if (2 : Fin 4) ≠ 0 ∧ j = 0 ∧ i = 2 then -(deriv a (x 0) / a (x 0))
      else 0 := by
  have hdiag : ∀ A : Fin 4, flrwTetradInv a x 2 A =
      if (2 : Fin 4) = A then ![(1 : ℝ), (a (x 0))⁻¹, (a (x 0))⁻¹, (a (x 0))⁻¹] 2 else 0 := by
    intro A
    simp [flrwTetradInv, Matrix.diagonal_apply]
  rw [Tetrad.weitzenbockTorsion_eq]
  simp only [flrwTetradFrame, hdiag, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
    ↓reduceIte, flrwTetrad_coordDeriv_eq]
  fin_cases i <;> fin_cases j <;> simp [div_eq_inv_mul]

private lemma flrwTetradFrame_weitzenbockTorsion_eq_k3 (a : ℝ → ℝ) (x : Fin 4 → ℝ)
    (ha : a (x 0) ≠ 0) (i j : Fin 4) :
    (flrwTetradFrame a x ha).weitzenbockTorsion (flrwTetradDeriv a x) 3 i j =
      if (3 : Fin 4) ≠ 0 ∧ i = 0 ∧ j = 3 then deriv a (x 0) / a (x 0)
      else if (3 : Fin 4) ≠ 0 ∧ j = 0 ∧ i = 3 then -(deriv a (x 0) / a (x 0))
      else 0 := by
  have hdiag : ∀ A : Fin 4, flrwTetradInv a x 3 A =
      if (3 : Fin 4) = A then ![(1 : ℝ), (a (x 0))⁻¹, (a (x 0))⁻¹, (a (x 0))⁻¹] 3 else 0 := by
    intro A
    simp [flrwTetradInv, Matrix.diagonal_apply]
  rw [Tetrad.weitzenbockTorsion_eq]
  simp only [flrwTetradFrame, hdiag, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
    ↓reduceIte, flrwTetrad_coordDeriv_eq]
  fin_cases i <;> fin_cases j <;> simp [div_eq_inv_mul]

private lemma flrwTetradFrame_weitzenbockTorsion_eq (a : ℝ → ℝ) (x : Fin 4 → ℝ)
    (ha : a (x 0) ≠ 0) (k i j : Fin 4) :
    (flrwTetradFrame a x ha).weitzenbockTorsion (flrwTetradDeriv a x) k i j =
      if k ≠ 0 ∧ i = 0 ∧ j = k then deriv a (x 0) / a (x 0)
      else if k ≠ 0 ∧ j = 0 ∧ i = k then -(deriv a (x 0) / a (x 0))
      else 0 := by
  fin_cases k
  · exact flrwTetradFrame_weitzenbockTorsion_eq_k0 a x ha i j
  · exact flrwTetradFrame_weitzenbockTorsion_eq_k1 a x ha i j
  · exact flrwTetradFrame_weitzenbockTorsion_eq_k2 a x ha i j
  · exact flrwTetradFrame_weitzenbockTorsion_eq_k3 a x ha i j

private lemma flrw_torsionTrace_eq (a : ℝ → ℝ) (x : Fin 4 → ℝ) (ha : a (x 0) ≠ 0) (j : Fin 4) :
    torsionTrace ((flrwTetradFrame a x ha).weitzenbockTorsion (flrwTetradDeriv a x)) j =
      if j = 0 then 3 * (deriv a (x 0) / a (x 0)) else 0 := by
  rw [torsionTrace, Fin.sum_univ_four]
  simp only [flrwTetradFrame_weitzenbockTorsion_eq]
  fin_cases j <;> simp
  ring

private lemma flrw_superpotential_eq (a : ℝ → ℝ) (x : Fin 4 → ℝ) (ha : a (x 0) ≠ 0)
    (k i j : Fin 4) :
    superpotential (flrwCartesianMetricTensor a x ha)
        ((flrwTetradFrame a x ha).weitzenbockTorsion (flrwTetradDeriv a x)) k i j =
      if k ≠ 0 ∧ i = 0 ∧ j = k then -(a (x 0) ^ 2 * (deriv a (x 0) / a (x 0)))
      else if k ≠ 0 ∧ j = 0 ∧ i = k then a (x 0) ^ 2 * (deriv a (x 0) / a (x 0))
      else 0 := by
  have hg : ∀ r p : Fin 4, (flrwCartesianMetricTensor a x ha).g r p =
      if r = p then ![-1, a (x 0) ^ 2, a (x 0) ^ 2, a (x 0) ^ 2] r else 0 := by
    intro r p
    simp [flrwCartesianMetricTensor, Matrix.diagonal_apply]
  simp only [superpotential, hg, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
    ↓reduceIte, flrwTetradFrame_weitzenbockTorsion_eq, flrw_torsionTrace_eq]
  fin_cases k <;> fin_cases i <;> fin_cases j <;> simp <;> ring

/-- Exact agreement between the general teleparallel torsion scalar `torsionScalar` applied to the
flat FLRW comoving tetrad `flrwTetradFrame` and the closed-form scalar `flrwTorsionScalar`. -/
lemma torsionScalar_flrw_eq_flrwTorsionScalar (a : ℝ → ℝ) (x : Fin 4 → ℝ) (ha : a (x 0) ≠ 0) :
    torsionScalar (flrwCartesianMetricTensor a x ha)
        ((flrwTetradFrame a x ha).weitzenbockTorsion (flrwTetradDeriv a x)) =
      flrwTorsionScalar a (x 0) := by
  have hg : ∀ r p : Fin 4, (flrwCartesianMetricTensor a x ha).g r p =
      if r = p then ![-1, a (x 0) ^ 2, a (x 0) ^ 2, a (x 0) ^ 2] r else 0 := by
    intro r p
    simp [flrwCartesianMetricTensor, Matrix.diagonal_apply]
  have hginv : ∀ r p : Fin 4, (flrwCartesianMetricTensor a x ha).ginv r p =
      if r = p then ![-1, (a (x 0) ^ 2)⁻¹, (a (x 0) ^ 2)⁻¹, (a (x 0) ^ 2)⁻¹] r else 0 := by
    intro r p
    simp [flrwCartesianMetricTensor, Matrix.diagonal_apply]
  simp only [torsionScalar, hginv, hg, ite_mul, zero_mul, mul_ite, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  simp only [flrw_superpotential_eq, flrwTetradFrame_weitzenbockTorsion_eq, Fin.sum_univ_four]
  simp [flrwTorsionScalar]
  field_simp [ha]
  ring

/-- Exact teleparallel-to-Levi-Civita scalar curvature equivalence on flat FLRW spacetime (`k = 0`):
`FLRWSpacetime.ricciScalar ⟨a, 0⟩ x = -T + B`. -/
lemma ricciScalar_flrw_flat_eq_neg_torsion_add_boundary (a : ℝ → ℝ) (x : Fin 4 → ℝ)
    (ha : a (x 0) ≠ 0) (hr : x 1 ≠ 0) (hsin : Real.sin (x 2) ≠ 0)
    (ha_diff : ∀ᶠ t in nhds (x 0), DifferentiableAt ℝ a t)
    (ha2 : DifferentiableAt ℝ (deriv a) (x 0)) :
    (FLRWSpacetime.mk a 0).toCoordinateMetric.ricciScalar x =
      -flrwTorsionScalar a (x 0) + flrwBoundaryTerm a (x 0) := by
  have hkr : 1 - (0 : ℝ) * (x 1) ^ 2 ≠ 0 := by norm_num
  rw [FLRWSpacetime.ricciScalar ⟨a, 0⟩ x ha hr hkr hsin ha_diff ha2]
  simp only [flrwTorsionScalar, flrwBoundaryTerm]
  ring

/-- For a Physlib `Cosmology.FLRW` universe, `flrwTorsionScalar` reproduces `6 H²` in terms of
`Cosmology.FLRW.FriedmannEquation.hubbleConstant` (in units `c = 1`). -/
lemma flrwTorsionScalar_ofCosmology (U : Cosmology.FLRW) {t : Time} (ht : t ∈ U.I) :
    flrwTorsionScalar (flrwScaleFactorOfReal 1 U) t.val =
      6 * (Cosmology.FLRW.FriedmannEquation.hubbleConstant U.a t) ^ 2 := by
  have hd := deriv_flrwScaleFactorOfReal_eq 1 U ht
  have ha := flrwScaleFactorOfReal_mul 1 U t
  simp only [SpeedOfLight.val_one, one_mul, div_one] at hd ha
  simp only [flrwTorsionScalar, hd, ha, Cosmology.FLRW.FriedmannEquation.hubbleConstant]

end Teleparallel

end Modified

end GeneralRelativity
