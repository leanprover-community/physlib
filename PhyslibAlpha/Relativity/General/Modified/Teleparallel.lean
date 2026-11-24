/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import PhyslibAlpha.Relativity.General.FLRW.Pipeline
public import PhyslibAlpha.Relativity.General.Modified.EinsteinCartan
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!

# Teleparallel Equivalent of General Relativity (TEGR) and `f(T)` gravity

Weitzenböck connection, teleparallel torsion and superpotential tensors, flat FLRW tetrad cosmology,
exact equivalence `R_LC = -T + B` with the Levi-Civita scalar curvature `FLRW.scalarOf_flrw`, and
`f(T)` modified Friedmann equations.

## i. Overview

In the Teleparallel Equivalent of General Relativity (TEGR), gravitational dynamics is formulated in
terms of an orthonormal tetrad (vierbein) `e^A_i` and its curvature-free Weitzenböck affine
connection `Γ^k_{ij} = e_A^k ∂_i e^A_j`, rather than the torsion-free Levi-Civita connection.
Because `Γ = Γ_LC + K` (`EinsteinCartan.connection_unique`), the Levi-Civita Ricci scalar `R_LC`
differs from minus the quadratic teleparallel torsion scalar `T = S_k^{ij} T^k_{ij}` by a total
four-divergence boundary term `B = (2 / e) ∂_i (e T^m_{m}{}^i)`:
`R_LC = -T + B`.

Consequently, the Einstein–Hilbert action `∫ e R_LC d⁴x` and the TEGR action `∫ e (-T) d⁴x` yield
identical classical field equations, while non-linear `f(T)` extensions (`ℒ = T + F(T)`) modify the
Friedmann equation to `3 H² + ½ F(6 H²) - 6 H² F'(6 H²) = 8 π G ρ`.

## ii. Key results

- `weitzenbockConn`, `weitzenbockTorsion`, `weitzenbockTorsion_eq`, `weitzenbockTorsion_antisymm` :
  Weitzenböck connection and torsion from a tetrad and its partial derivatives.
- `superpotential`, `torsionScalar` : teleparallel superpotential `S_k^{ij}` and quadratic torsion
  scalar `T`.
- `flrwTetrad`, `flrwTetradInv`, `flrwTetrad_mul_inv` : diagonal flat FLRW comoving tetrad
  `e^A_i = diag(1, a(t), a(t), a(t))` and its inverse.
- `flrwTorsionScalar`, `flrwBoundaryTerm`, `scalarOf_flrw_flat_eq_neg_torsion_add_boundary` :
  exact identity `scalarOf (flrwMetric a 0) (flrwMetricInv a 0) x = -T + B` bridging TEGR to
  `FLRW.scalarOf_flrw`.
- `fTFriedmannLHS`, `fTFriedmannLHS_tegr`, `fTFriedmannLHS_quadratic` : modified `f(T)` Friedmann
  equation and TEGR recovery.

## iii. Table of contents

- A. Weitzenböck connection, torsion, and superpotential
- B. Flat FLRW teleparallel cosmology and `R_LC = -T + B`
- C. `f(T)` modified Friedmann cosmology

## iv. References

* Albert Einstein, *Riemann-Geometrie mit Aufrechterhaltung des Begriffes des Fernparallelismus*,
  *Sitzungsberichte der Preussischen Akademie der Wissenschaften, Physikalisch-Mathematische
  Klasse* (1928). [ref: Einstein1928]
* Kenji Hayashi and Takeshi Shirafuji, *New General Relativity*, *Physical Review D* (1979). [ref:
  HayashiShirafuji1979]
* José W. Maluf, *The Teleparallel Equivalent of General Relativity*, *Annalen der Physik* (2013)
  (https://arxiv.org/abs/1303.3897). [ref: Maluf2013]
* Rafael Ferraro and Franco Fiorini, *Modified Teleparallel Gravity: Inflation without Inflaton*,
  *Physical Review D* (2007). [ref: FerraroFiorini2007]
* Gabriel R. Bengochea and Rafael Ferraro, *Dark Torsion as the Cosmic Speed-Up*, *Physical Review
  D* (2009) (https://arxiv.org/abs/0812.1205). [ref: BengocheaFerraro2009]
* Eric V. Linder, *Einstein's Other Gravity and the Acceleration of the Universe*, *Physical
  Review D* (2010) (https://arxiv.org/abs/1005.3039). [ref: Linder2010]
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
open GeneralRelativity.Modified.EinsteinCartan

/-!

## A. Weitzenböck connection, torsion, and superpotential

-/

/-- Weitzenböck affine connection `Γ^k_{ij} = ∑_A e_A^k ∂_i e^A_j` constructed from the inverse
tetrad `einv A k = e_A^k` and tetrad partial derivatives `de i A j = ∂_i e^A_j`. -/
def weitzenbockConn {n : ℕ} (einv : Tensor2 n) (de : Fin n → Tensor2 n) : Conn n :=
  fun k i j => ∑ A : Fin n, einv A k * de i A j

/-- Weitzenböck torsion tensor `T^k_{ij} = Γ^k_{ij} - Γ^k_{ji}`. -/
def weitzenbockTorsion {n : ℕ} (einv : Tensor2 n) (de : Fin n → Tensor2 n) : Conn n :=
  torsion (weitzenbockConn einv de)

/-- Explicit tetrad-derivative formula for the Weitzenböck torsion:
`T^k_{ij} = ∑_A e_A^k (∂_i e^A_j - ∂_j e^A_i)`. -/
lemma weitzenbockTorsion_eq {n : ℕ} (einv : Tensor2 n) (de : Fin n → Tensor2 n) (k i j : Fin n) :
    weitzenbockTorsion einv de k i j = ∑ A : Fin n, einv A k * (de i A j - de j A i) := by
  unfold weitzenbockTorsion torsion weitzenbockConn
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun A _ => by ring

/-- Antisymmetry of the Weitzenböck torsion in its lower indices:
`T^k_{ij} = -T^k_{ji}`. -/
lemma weitzenbockTorsion_antisymm {n : ℕ} (einv : Tensor2 n) (de : Fin n → Tensor2 n)
    (k i j : Fin n) :
    weitzenbockTorsion einv de k i j = -weitzenbockTorsion einv de k j i :=
  torsion_antisymm (weitzenbockConn einv de) k i j

/-- Covariant teleparallel superpotential
`S_{k i j} = ½ (g_{ip} T^p_{kj} - g_{jp} T^p_{ki} - g_{kp} T^p_{ij}) + g_{ki} T^m_{jm}
- g_{kj} T^m_{im}`, antisymmetric in its last two indices `(i, j)`. -/
noncomputable def superpotential (M : MetricTensor 4) (T : Conn 4) : Conn 4 :=
  fun k i j =>
    (1 / 2) *
      ((∑ p : Fin 4, M.g i p * T p k j)
        - (∑ p : Fin 4, M.g j p * T p k i)
        - (∑ p : Fin 4, M.g k p * T p i j))
      + M.g k i * torsionTrace T j
      - M.g k j * torsionTrace T i

/-- Antisymmetry of the teleparallel superpotential in its last two indices `(i, j)` whenever
`T` is antisymmetric in its lower indices. -/
lemma superpotential_antisymm (M : MetricTensor 4) (T : Conn 4)
    (hT : ∀ k i j, T k i j = -T k j i) (k i j : Fin 4) :
    superpotential M T k i j = -superpotential M T k j i := by
  unfold superpotential
  have hsum : (∑ p : Fin 4, M.g k p * T p i j) = -(∑ p : Fin 4, M.g k p * T p j i) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun p _ => by rw [hT p i j]; ring
  rw [hsum]
  ring

/-- Quadratic teleparallel torsion scalar `T = ∑_{k,i,j} S_{k i j} T^k_{i j}` (in orthonormal or
index-raised contraction). -/
noncomputable def torsionScalar (M : MetricTensor 4) (T : Conn 4) : ℝ :=
  ∑ k : Fin 4, ∑ p : Fin 4, ∑ i : Fin 4, ∑ j : Fin 4,
    M.ginv k p * superpotential M T p i j *
      (∑ q : Fin 4, ∑ r : Fin 4, M.ginv i q * M.ginv j r *
        (∑ s : Fin 4, M.g k s * T s q r))

/-!

## B. Flat FLRW teleparallel cosmology and `R_LC = -T + B`

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
    flrwTetradInv a x k k * pd 0 (fun y => flrwTetrad a y k k) x =
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
  rw [pd, hfun, hinv, div_eq_inv_mul]

/-- Flat FLRW teleparallel torsion scalar `T = 6 H² = 6 (a'(t) / a(t))²`. -/
noncomputable def flrwTorsionScalar (a : ℝ → ℝ) (t : ℝ) : ℝ :=
  6 * (deriv a t / a t) ^ 2

/-- Flat FLRW teleparallel total-divergence boundary term
`B = (2 / a³) ∂_t (3 a² a') = 6 (a'' / a + 2 (a' / a)²)`. -/
noncomputable def flrwBoundaryTerm (a : ℝ → ℝ) (t : ℝ) : ℝ :=
  6 * (deriv (deriv a) t / a t + 2 * (deriv a t / a t) ^ 2)

/-- Exact teleparallel-to-Levi-Civita scalar curvature equivalence on flat FLRW spacetime (`k = 0`):
`scalarOf (flrwMetric a 0) (flrwMetricInv a 0) x = -T + B`. -/
lemma scalarOf_flrw_flat_eq_neg_torsion_add_boundary (a : ℝ → ℝ) (x : Fin 4 → ℝ)
    (ha : a (x 0) ≠ 0) (hr : x 1 ≠ 0) (hsin : Real.sin (x 2) ≠ 0)
    (ha_diff : ∀ᶠ t in nhds (x 0), DifferentiableAt ℝ a t)
    (ha2 : DifferentiableAt ℝ (deriv a) (x 0)) :
    scalarOf (flrwMetric a 0) (flrwMetricInv a 0) x =
      -flrwTorsionScalar a (x 0) + flrwBoundaryTerm a (x 0) := by
  have hkr : 1 - 0 * (x 1) ^ 2 ≠ 0 := by norm_num
  rw [scalarOf_flrw a 0 x ha hr hkr hsin ha_diff ha2]
  unfold flrwTorsionScalar flrwBoundaryTerm
  ring

/-!

## C. `f(T)` modified Friedmann cosmology

-/

/-- Modified first Friedmann equation left-hand side for an `f(T) = T + F(T)` teleparallel gravity
action evaluated at `T = 6 H²`: `3 H² + ½ F(6 H²) - 6 H² F'(6 H²)`. -/
noncomputable def fTFriedmannLHS (H : ℝ) (F dF : ℝ → ℝ) : ℝ :=
  3 * H ^ 2 + (1 / 2) * F (6 * H ^ 2) - 6 * H ^ 2 * dF (6 * H ^ 2)

/-- In the Teleparallel Equivalent of General Relativity (`F = 0`, `dF = 0`), the `f(T)` Friedmann
equation reduces identically to the standard General Relativity Friedmann left-hand side `3 H²`. -/
lemma fTFriedmannLHS_tegr (H : ℝ) :
    fTFriedmannLHS H (fun _ => 0) (fun _ => 0) = 3 * H ^ 2 := by
  unfold fTFriedmannLHS
  ring

/-- For a quadratic teleparallel correction `F(T) = α T²` (`dF(T) = 2 α T`), the modified Friedmann
left-hand side evaluates to `3 H² - 54 α H⁴`. -/
lemma fTFriedmannLHS_quadratic (H α : ℝ) :
    fTFriedmannLHS H (fun T => α * T ^ 2) (fun T => 2 * α * T) =
      3 * H ^ 2 - 54 * α * H ^ 4 := by
  unfold fTFriedmannLHS
  ring

end Teleparallel

end Modified

end GeneralRelativity
