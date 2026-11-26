/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import PhyslibAlpha.Relativity.General.Linearized.TraceReversed
import Mathlib.Tactic.Ring

/-!

# Linearized connection and curvature tensors

First-order linearized Christoffel, Riemann, Ricci, scalar, and Einstein tensors for a
`MetricPerturbation` around Minkowski spacetime.

## i. Overview

Given a `MetricPerturbation` `P` around `minkowskiMetric4`, this module defines the linearized
Christoffel symbols `linChristoffel`, Riemann tensor `linRiemann`, Ricci tensor `linRicci`,
scalar curvature `linScalar`, and Einstein tensor `linEinstein`. It proves index symmetries of
`linChristoffel` and `linRiemann` together with additivity of `linRiemann` for `C²` perturbations.

## ii. Key results

- `linChristoffel`, `linChristoffel_symm` : linearized Christoffel symbols and lower symmetry.
- `linRiemann`, `linRiemann_antisymm`, `linRiemann_add` : linearized Riemann tensor,
  antisymmetry, and additivity.
- `linRicci`, `linScalar`, `linEinstein` : linearized Ricci, scalar, and Einstein tensors.

## iii. Table of contents

- A. Linearized connection and curvature tensors

## iv. References

* R. M. Wald, *General Relativity* (1984), Ch. 4 (Sec. 4.4). [ref: wald_1984_general_relativity]
* C. W. Misner, K. S. Thorne, and J. A. Wheeler, *Gravitation* (1973), Ch. 18.
  [ref: mtw_1973_gravitation]
* S. M. Carroll, *Lecture Notes on General Relativity* (1997), Ch. 6
  (https://arxiv.org/pdf/gr-qc/9712019#page=144). [ref: Carroll1997]
-/

@[expose] public section

namespace GeneralRelativity

namespace Linearized

open Pipeline

/-!

## A. Linearized connection and curvature tensors

Perturbing flat Minkowski spacetime by `g = η + h` linearizes the Christoffel symbols and
curvature tensors in first-order partial derivatives of `P.h`.

-/

/-- Linearized Christoffel symbols `Γ^k_{ij} = ½ η^{km} (∂_j h_{mi} + ∂_i h_{mj} - ∂_m h_{ij})`. -/
noncomputable def linChristoffel (P : MetricPerturbation) (x : Fin 4 → ℝ)
    (k i j : Fin 4) : ℝ :=
  (1 / 2) * minkowskiMetric4 k k
    * (coordDeriv j (fun y => P.h y k i) x + coordDeriv i (fun y => P.h y k j) x
      - coordDeriv k (fun y => P.h y i j) x)

/-- Lower-index symmetry of linearized Christoffel symbols for a `MetricPerturbation`. -/
lemma linChristoffel_symm (P : MetricPerturbation) (x : Fin 4 → ℝ) (k i j : Fin 4) :
    linChristoffel P x k i j = linChristoffel P x k j i := by
  have hij : (fun y => P.h y i j) = fun y => P.h y j i := funext fun y => P.symm_apply y i j
  simp only [linChristoffel, hij]
  ring

/-- Linearized Riemann curvature tensor `R^r_{s m n} = ∂_m Γ^r_{n s} - ∂_n Γ^r_{m s}`. -/
noncomputable def linRiemann (P : MetricPerturbation) (x : Fin 4 → ℝ)
    (r s m n : Fin 4) : ℝ :=
  coordDeriv m (fun y => linChristoffel P y r n s) x
    - coordDeriv n (fun y => linChristoffel P y r m s) x

/-- Antisymmetry of `linRiemann` in its last two indices. -/
lemma linRiemann_antisymm (P : MetricPerturbation) (x : Fin 4 → ℝ) (r s m n : Fin 4) :
    linRiemann P x r s m n = -linRiemann P x r s n m := by
  simp only [linRiemann]
  ring

/-- Additivity of `linRiemann` for `C²` perturbations. -/
lemma linRiemann_add (P Q : MetricPerturbation) (x : Fin 4 → ℝ)
    (hP : P.IsC2At x) (hQ : Q.IsC2At x) (r s m n : Fin 4) :
    linRiemann (P.add Q) x r s m n = linRiemann P x r s m n + linRiemann Q x r s m n := by
  have nh1 : ∀ᶠ y in nhds x, P.IsC2At y := hP.eventually
  have nh2 : ∀ᶠ y in nhds x, Q.IsC2At y := hQ.eventually
  have hcongr : ∀ k i j,
      (fun y => linChristoffel (P.add Q) y k i j) =ᶠ[nhds x]
        fun y => linChristoffel P y k i j + linChristoffel Q y k i j := by
    intro k i j
    filter_upwards [nh1, nh2] with y hy1 hy2
    have d1 : ∀ a b, DifferentiableAt ℝ (fun z => P.h z a b) y :=
      fun a b => (hy1 a b).differentiableAt (by norm_num)
    have d2 : ∀ a b, DifferentiableAt ℝ (fun z => Q.h z a b) y :=
      fun a b => (hy2 a b).differentiableAt (by norm_num)
    simp only [linChristoffel, MetricPerturbation.add, Matrix.add_apply]
    rw [coordDeriv_add j y (slice_differentiableAt j (d1 k i)) (slice_differentiableAt j (d2 k i)),
      coordDeriv_add i y (slice_differentiableAt i (d1 k j)) (slice_differentiableAt i (d2 k j)),
      coordDeriv_add k y (slice_differentiableAt k (d1 i j)) (slice_differentiableAt k (d2 i j))]
    ring
  have hd_lin : ∀ R : MetricPerturbation, R.IsC2At x →
      ∀ k i j, DifferentiableAt ℝ (fun y => linChristoffel R y k i j) x := by
    intro R hR k i j
    simp only [linChristoffel]
    exact (((coordDeriv_differentiableAt j (hR k i)).add
      (coordDeriv_differentiableAt i (hR k j))).sub
      (coordDeriv_differentiableAt k (hR i j))).const_mul _
  simp only [linRiemann]
  rw [coordDeriv_congr_nhds m x (hcongr r n s),
    coordDeriv_congr_nhds n x (hcongr r m s),
    coordDeriv_add m x (slice_differentiableAt m (hd_lin P hP r n s))
      (slice_differentiableAt m (hd_lin Q hQ r n s)),
    coordDeriv_add n x (slice_differentiableAt n (hd_lin P hP r m s))
      (slice_differentiableAt n (hd_lin Q hQ r m s))]
  ring

/-- Linearized Ricci tensor `R^{(1)}_{ij} = ∑ r, R^r_{i r j}`. -/
noncomputable def linRicci (P : MetricPerturbation) (x : Fin 4 → ℝ) (i j : Fin 4) : ℝ :=
  ∑ r : Fin 4, linRiemann P x r i r j

/-- Linearized Ricci scalar `S^{(1)} = η^{ij} R^{(1)}_{ij}`. -/
noncomputable def linScalar (P : MetricPerturbation) (x : Fin 4 → ℝ) : ℝ :=
  ∑ i : Fin 4, minkowskiMetric4 i i * linRicci P x i i

/-- Linearized Einstein tensor `G^{(1)}_{ij} = R^{(1)}_{ij} - ½ η_{ij} S^{(1)}`. -/
noncomputable def linEinstein (P : MetricPerturbation) (x : Fin 4 → ℝ)
    (i j : Fin 4) : ℝ :=
  linRicci P x i j - (1 / 2) * minkowskiMetric4 i j * linScalar P x

end Linearized

end GeneralRelativity
