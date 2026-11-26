/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import PhyslibAlpha.Relativity.General.Linearized.LinearizedEinstein
public import PhyslibAlpha.Relativity.General.Linearized.MinkowskiDalembertian
import Mathlib.Tactic.Ring

/-!

# Lorenz gauge and linearized wave equation

The Lorenz (harmonic/de Donder) gauge condition `∂^k h̄_{kj} = 0` and reduction of the linearized
Einstein tensor to `-(1/2) □_η h̄_{ij}`.

## i. Overview

Expressing the linearized Ricci tensor and Ricci scalar in terms of the trace-reversed
perturbation `P.traceReversed` and the Lorenz gauge divergence `lorenzDivergence P`, the scalar
wave term cancels in the linearized Einstein tensor `linearizedEinstein P`. Consequently, whenever
`IsLorenzGauge P` holds on a neighborhood of `x`, `linearizedEinstein P` reduces to the flat-space
wave operator `-(1/2) □_η h̄_{ij}`.

## ii. Key results

- `lorenzDivergence`, `IsLorenzGauge` : Lorenz gauge divergence vector and vanishing condition.
- `linearizedRicci_in_traceReversed`, `linearizedEinstein_in_traceReversed` : expansion in
  `P.traceReversed` and `lorenzDivergence`.
- `linearizedEinstein_lorenz_gauge` : Lorenz-gauge wave equation
  `linearizedEinstein = -(1/2) □_η h̄`.

## iii. Table of contents

- A. Lorenz gauge and wave equation reduction

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

open Pipeline

/-!

## A. Lorenz gauge and wave equation reduction

Using Schwarz symmetry `∂_μ ∂_ν = ∂_ν ∂_μ` on the second derivatives of `h̄` cancels the mixed
cross terms and scalar trace, reducing `linearizedEinstein` in Lorenz gauge `∂^k h̄_{kj} = 0` to
the flat-space gravitational wave operator `-(1/2) □_η h̄_{ij}`.

-/

/-- Lorenz (harmonic/de Donder) gauge divergence vector `∂^k h̄_{kj} = η^{kk} ∂_k h̄_{kj}`. -/
noncomputable def lorenzDivergence (P : MetricPerturbation) (x : Fin 4 → ℝ) (j : Fin 4) : ℝ :=
  ∑ k : Fin 4, minkowskiMetric4 k k * coordDeriv k (fun y => P.traceReversed.h y k j) x

/-- Lorenz gauge condition `lorenzDivergence P x j = 0`. -/
def IsLorenzGauge (P : MetricPerturbation) (x : Fin 4 → ℝ) (j : Fin 4) : Prop :=
  lorenzDivergence P x j = 0

private lemma linearizedChristoffel_trace (P : MetricPerturbation) (y : Fin 4 → ℝ)
    (hP : ∀ a b, DifferentiableAt ℝ (fun z => P.h z a b) y) (i : Fin 4) :
    (∑ r : Fin 4, linearizedChristoffel P y r r i) =
      (1 / 2) * coordDeriv i (fun z => perturbationTrace (P.h z)) y := by
  have heq : ∀ r, (fun z => P.h z r i) = fun z => P.h z i r :=
    fun r => funext fun z => P.symm_apply z r i
  simp only [linearizedChristoffel, heq, add_sub_cancel_right]
  have hsum : (∑ r : Fin 4, (1 / 2) * minkowskiMetric4 r r * coordDeriv i (fun z => P.h z r r) y)
      = (1 / 2) * coordDeriv i (fun z => ∑ r : Fin 4, minkowskiMetric4 r r * P.h z r r) y := by
    rw [coordDeriv_sum i (fun r z => minkowskiMetric4 r r * P.h z r r) y
      (fun r => (slice_differentiableAt i (hP r r)).const_mul _), Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [coordDeriv_const_mul, mul_assoc]
  simpa [perturbationTrace] using hsum

private lemma pd_linearizedChristoffel_diag (P : MetricPerturbation) (x : Fin 4 → ℝ)
    (hP : P.IsC2At x) (i j : Fin 4) :
    (∑ r : Fin 4, coordDeriv j (fun y => linearizedChristoffel P y r r i) x)
      = -(1 / 2) *
        coordDeriv j (coordDeriv i (fun z => perturbationTrace (P.traceReversed.h z))) x := by
  rw [← coordDeriv_sum j (fun r y => linearizedChristoffel P y r r i) x
    fun r => slice_differentiableAt j (differentiableAt_linearizedChristoffel hP r r i)]
  have hcongr : (fun y => ∑ r : Fin 4, linearizedChristoffel P y r r i) =ᶠ[nhds x]
      fun y => -(1 / 2) * coordDeriv i (fun z => perturbationTrace (P.traceReversed.h z)) y := by
    filter_upwards [hP.eventually] with y hy
    rw [linearizedChristoffel_trace P y
      (fun a b => (hy a b).differentiableAt (by norm_num)) i]
    have hT : (fun z => perturbationTrace (P.h z)) =
        fun z => -perturbationTrace (P.traceReversed.h z) := by
      funext z; simp [MetricPerturbation.traceReversed, traceReversed_trace]
    rw [hT]
    have hdneg : coordDeriv i (fun z => -perturbationTrace (P.traceReversed.h z)) y
        = -coordDeriv i (fun z => perturbationTrace (P.traceReversed.h z)) y := by
      have : (fun z => -perturbationTrace (P.traceReversed.h z))
          = fun z => (-1 : ℝ) * perturbationTrace (P.traceReversed.h z) := by funext z; ring
      rw [this, coordDeriv_const_mul]; ring
    rw [hdneg]
    ring
  rw [coordDeriv_congr_nhds j x hcongr, coordDeriv_const_mul]

private lemma linearizedChristoffel_eventuallyEq_traceReversed (P : MetricPerturbation)
    (x : Fin 4 → ℝ) (hP : P.IsC2At x) (i j r : Fin 4) :
    (fun y => linearizedChristoffel P y r j i) =ᶠ[nhds x] fun y =>
      (1 / 2) * minkowskiMetric4 r r * (coordDeriv i (fun z => P.traceReversed.h z r j) y
        + coordDeriv j (fun z => P.traceReversed.h z r i) y
        - coordDeriv r (fun z => P.traceReversed.h z j i) y)
        - (1 / 4) * minkowskiMetric4 r r * (minkowskiMetric4 r j *
            coordDeriv i (fun z => perturbationTrace (P.traceReversed.h z)) y
          + minkowskiMetric4 r i *
            coordDeriv j (fun z => perturbationTrace (P.traceReversed.h z)) y
          - minkowskiMetric4 j i *
            coordDeriv r (fun z => perturbationTrace (P.traceReversed.h z)) y) := by
  filter_upwards [hP.eventually] with y hy
  have hb_c2 : P.traceReversed.IsC2At y := hy.traceReversed
  have hT_c2 : ContDiffAt ℝ 2 (fun z => perturbationTrace (P.traceReversed.h z)) y :=
    contDiffAt_perturbationTrace hb_c2
  have hcd : ∀ p q, (fun z => P.h z p q) = fun z =>
      P.traceReversed.h z p q
        - (1 / 2) * minkowskiMetric4 p q * perturbationTrace (P.traceReversed.h z) := by
    intro p q; funext z
    have hi := congrArg (fun M => M p q) (traceReversed_involutive (P.h z))
    simpa [MetricPerturbation.traceReversed, traceReversed, Matrix.of_apply] using hi.symm
  have d_b : ∀ p q, DifferentiableAt ℝ (fun z => P.traceReversed.h z p q) y :=
    fun p q => (hb_c2 p q).differentiableAt (by norm_num)
  have d_T : DifferentiableAt ℝ (fun z => perturbationTrace (P.traceReversed.h z)) y :=
    hT_c2.differentiableAt (by norm_num)
  simp only [linearizedChristoffel, hcd]
  rw [coordDeriv_sub i y (slice_differentiableAt i (d_b r j))
      ((slice_differentiableAt i d_T).const_mul _),
    coordDeriv_sub j y (slice_differentiableAt j (d_b r i))
      ((slice_differentiableAt j d_T).const_mul _),
    coordDeriv_sub r y (slice_differentiableAt r (d_b j i))
      ((slice_differentiableAt r d_T).const_mul _),
    coordDeriv_const_mul, coordDeriv_const_mul, coordDeriv_const_mul]
  ring

private lemma coordDeriv_traceReversed_differentiableAt (P : MetricPerturbation)
    (x : Fin 4 → ℝ) (hP : P.IsC2At x) (p q μ : Fin 4) :
    DifferentiableAt ℝ (coordDeriv μ fun z => P.traceReversed.h z p q) x :=
  coordDeriv_differentiableAt μ (hP.traceReversed p q)

private lemma coordDeriv_perturbationTrace_traceReversed_differentiableAt
    (P : MetricPerturbation) (x : Fin 4 → ℝ) (hP : P.IsC2At x) (μ : Fin 4) :
    DifferentiableAt ℝ (coordDeriv μ fun z => perturbationTrace (P.traceReversed.h z)) x :=
  coordDeriv_differentiableAt μ (contDiffAt_perturbationTrace hP.traceReversed)

private lemma sum_eta_diag_mul_coordDeriv_perturbationTrace (P : MetricPerturbation)
    (x : Fin 4 → ℝ) (k l : Fin 4) :
    (∑ r : Fin 4, (1 / 4 : ℝ) * (minkowskiMetric4 r r * minkowskiMetric4 r k) *
      coordDeriv l (coordDeriv r fun z => perturbationTrace (P.traceReversed.h z)) x)
      = (1 / 4) *
        coordDeriv l (coordDeriv k fun z => perturbationTrace (P.traceReversed.h z)) x := by
  fin_cases k <;> simp

private lemma pd_linearizedChristoffel_traceReversed (P : MetricPerturbation) (x : Fin 4 → ℝ)
    (hP : P.IsC2At x) (i j r : Fin 4) :
    coordDeriv r (fun y => linearizedChristoffel P y r j i) x =
      (1 / 2) * minkowskiMetric4 r r *
        coordDeriv i (coordDeriv r fun z => P.traceReversed.h z r j) x
      + (1 / 2) * minkowskiMetric4 r r *
        coordDeriv j (coordDeriv r fun z => P.traceReversed.h z r i) x
      - (1 / 2) * minkowskiMetric4 r r *
        coordDeriv r (coordDeriv r fun z => P.traceReversed.h z j i) x
      - (1 / 4) * (minkowskiMetric4 r r * minkowskiMetric4 r j) *
          coordDeriv i (coordDeriv r fun z => perturbationTrace (P.traceReversed.h z)) x
      - (1 / 4) * (minkowskiMetric4 r r * minkowskiMetric4 r i) *
          coordDeriv j (coordDeriv r fun z => perturbationTrace (P.traceReversed.h z)) x
      + (1 / 4) * minkowskiMetric4 j i *
          (minkowskiMetric4 r r *
            coordDeriv r (coordDeriv r fun z => perturbationTrace (P.traceReversed.h z)) x) := by
  have hb := hP.traceReversed
  have hT := contDiffAt_perturbationTrace hb
  have db := coordDeriv_traceReversed_differentiableAt P x hP
  have dT := coordDeriv_perturbationTrace_traceReversed_differentiableAt P x hP
  have h1 : DifferentiableAt ℝ (fun y => (1 / 2 : ℝ) * minkowskiMetric4 r r *
      (coordDeriv i (fun z => P.traceReversed.h z r j) y
        + coordDeriv j (fun z => P.traceReversed.h z r i) y
        - coordDeriv r (fun z => P.traceReversed.h z j i) y)) x :=
    (((db r j i).add (db r i j)).sub (db j i r)).const_mul _
  have h2 : DifferentiableAt ℝ (fun y => (1 / 4 : ℝ) * minkowskiMetric4 r r *
      (minkowskiMetric4 r j *
          coordDeriv i (fun z => perturbationTrace (P.traceReversed.h z)) y
        + minkowskiMetric4 r i *
          coordDeriv j (fun z => perturbationTrace (P.traceReversed.h z)) y
        - minkowskiMetric4 j i *
          coordDeriv r (fun z => perturbationTrace (P.traceReversed.h z)) y)) x :=
    ((((dT i).const_mul _).add ((dT j).const_mul _)).sub ((dT r).const_mul _)).const_mul _
  rw [coordDeriv_congr_nhds r x (linearizedChristoffel_eventuallyEq_traceReversed P x hP i j r),
    coordDeriv_sub r x (slice_differentiableAt r h1) (slice_differentiableAt r h2),
    coordDeriv_const_mul, coordDeriv_const_mul,
    coordDeriv_sub r x ((slice_differentiableAt r (db r j i)).add
      (slice_differentiableAt r (db r i j))) (slice_differentiableAt r (db j i r)),
    coordDeriv_add r x (slice_differentiableAt r (db r j i)) (slice_differentiableAt r (db r i j)),
    coordDeriv_sub r x (((slice_differentiableAt r (dT i)).const_mul _).add
      ((slice_differentiableAt r (dT j)).const_mul _))
      ((slice_differentiableAt r (dT r)).const_mul _),
    coordDeriv_add r x ((slice_differentiableAt r (dT i)).const_mul _)
      ((slice_differentiableAt r (dT j)).const_mul _),
    coordDeriv_const_mul, coordDeriv_const_mul, coordDeriv_const_mul,
    coordDeriv_comm r i (hb r j), coordDeriv_comm r j (hb r i),
    coordDeriv_comm r i hT, coordDeriv_comm r j hT]
  ring

private lemma pd_lorenzDivergence (P : MetricPerturbation) (x : Fin 4 → ℝ)
    (hP : P.IsC2At x) (i j : Fin 4) :
    coordDeriv i (fun y => lorenzDivergence P y j) x = ∑ r : Fin 4,
      minkowskiMetric4 r r * coordDeriv i (coordDeriv r fun z => P.traceReversed.h z r j) x := by
  simp only [lorenzDivergence]
  rw [coordDeriv_sum i _ x fun r =>
    slice_differentiableAt i
      ((coordDeriv_differentiableAt r (hP.traceReversed r j)).const_mul _)]
  refine Finset.sum_congr rfl fun r _ => coordDeriv_const_mul i (minkowskiMetric4 r r) x

/-- Expansion of `linearizedRicci P x i j` in terms of `P.traceReversed` and
`lorenzDivergence P`. -/
lemma linearizedRicci_in_traceReversed (P : MetricPerturbation) (x : Fin 4 → ℝ)
    (hP : P.IsC2At x) (i j : Fin 4) :
    linearizedRicci P x i j =
      -(1 / 2) * minkowskiDalembertian (fun y => P.traceReversed.h y i j) x
        + (1 / 2) * coordDeriv i (fun y => lorenzDivergence P y j) x
        + (1 / 2) * coordDeriv j (fun y => lorenzDivergence P y i) x
        + (1 / 4) * minkowskiMetric4 i j *
          minkowskiDalembertian (fun y => perturbationTrace (P.traceReversed.h y)) x := by
  have hT := contDiffAt_perturbationTrace hP.traceReversed
  have hbox_sym : minkowskiDalembertian (fun y => P.traceReversed.h y j i) x =
      minkowskiDalembertian (fun y => P.traceReversed.h y i j) x := by
    have hbs : (fun y => P.traceReversed.h y j i) = fun y => P.traceReversed.h y i j :=
      funext fun y => P.traceReversed.symm_apply y j i
    simp [hbs]
  simp only [linearizedRicci, linearizedRiemann, Finset.sum_sub_distrib,
    pd_linearizedChristoffel_traceReversed P x hP,
    pd_linearizedChristoffel_diag P x hP i j, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [pd_lorenzDivergence P x hP i j, pd_lorenzDivergence P x hP j i, ← hbox_sym,
    minkowskiMetric4_symm.apply i j,
    sum_eta_diag_mul_coordDeriv_perturbationTrace P x j i,
    sum_eta_diag_mul_coordDeriv_perturbationTrace P x i j,
    coordDeriv_comm j i hT]
  have hs1 : (∑ r : Fin 4, (1 / 2 : ℝ) * minkowskiMetric4 r r *
      coordDeriv i (coordDeriv r fun z => P.traceReversed.h z r j) x)
      = (1 / 2) * ∑ r : Fin 4, minkowskiMetric4 r r *
        coordDeriv i (coordDeriv r fun z => P.traceReversed.h z r j) x := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun _ _ => by ring
  have hs2 : (∑ r : Fin 4, (1 / 2 : ℝ) * minkowskiMetric4 r r *
      coordDeriv j (coordDeriv r fun z => P.traceReversed.h z r i) x)
      = (1 / 2) * ∑ r : Fin 4, minkowskiMetric4 r r *
        coordDeriv j (coordDeriv r fun z => P.traceReversed.h z r i) x := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun _ _ => by ring
  have hs3 : (∑ r : Fin 4, (1 / 2 : ℝ) * minkowskiMetric4 r r *
      coordDeriv r (coordDeriv r fun z => P.traceReversed.h z j i) x)
      = (1 / 2) * minkowskiDalembertian (fun y => P.traceReversed.h y j i) x := by
    simp only [minkowskiDalembertian, Finset.mul_sum]
    refine Finset.sum_congr rfl fun _ _ => by ring
  rw [hs1, hs2, hs3]
  simp only [minkowskiDalembertian]
  ring

private lemma minkowskiDalembertian_perturbationTrace (Q : MetricPerturbation) (x : Fin 4 → ℝ)
    (hQ : Q.IsC2At x) :
    (∑ i : Fin 4, minkowskiMetric4 i i * minkowskiDalembertian (fun y => Q.h y i i) x) =
      minkowskiDalembertian (fun y => perturbationTrace (Q.h y)) x := by
  simp only [minkowskiDalembertian, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun μ _ => ?_
  have hdμ : ∀ i, DifferentiableAt ℝ (coordDeriv μ fun y => Q.h y i i) x :=
    fun i => coordDeriv_differentiableAt μ (hQ i i)
  have hcongr :
      (fun y => ∑ i : Fin 4, minkowskiMetric4 i i * Q.h y i i) =
        fun y => perturbationTrace (Q.h y) :=
    funext fun y => (metricTrace_minkowski (Q.h y)).symm
  have hpd1 : ∀ y, (∀ i, DifferentiableAt ℝ (fun z => Q.h z i i) y) →
      coordDeriv μ (fun z => perturbationTrace (Q.h z)) y =
        ∑ i : Fin 4, minkowskiMetric4 i i * coordDeriv μ (fun z => Q.h z i i) y := by
    intro y hy
    rw [← hcongr, coordDeriv_sum μ _ y fun i => (slice_differentiableAt μ (hy i)).const_mul _]
    refine Finset.sum_congr rfl fun i _ => coordDeriv_const_mul μ (minkowskiMetric4 i i) y
  have hev : coordDeriv μ (fun z => perturbationTrace (Q.h z)) =ᶠ[nhds x] fun y =>
      ∑ i : Fin 4, minkowskiMetric4 i i * coordDeriv μ (fun z => Q.h z i i) y := by
    filter_upwards [hQ.eventually] with y hy
    exact hpd1 y fun i => (hy i i).differentiableAt (by norm_num)
  rw [coordDeriv_congr_nhds μ x hev,
    coordDeriv_sum μ _ x fun i => slice_differentiableAt μ ((hdμ i).const_mul _),
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [coordDeriv_const_mul, mul_left_comm]

private lemma linearizedRicciScalar_in_traceReversed (P : MetricPerturbation) (x : Fin 4 → ℝ)
    (hP : P.IsC2At x) :
    linearizedRicciScalar P x =
      (1 / 2) * minkowskiDalembertian (fun y => perturbationTrace (P.traceReversed.h y)) x
        + ∑ a : Fin 4, minkowskiMetric4 a a * coordDeriv a (fun y => lorenzDivergence P y a) x := by
  have hbox_trace := minkowskiDalembertian_perturbationTrace P.traceReversed x hP.traceReversed
  have heta_sq : (∑ i : Fin 4, minkowskiMetric4 i i * minkowskiMetric4 i i) = 4 := by
    simp [Fin.sum_univ_four]
    norm_num
  simp only [linearizedRicciScalar, linearizedRicci_in_traceReversed P x hP, mul_add,
    Finset.sum_add_distrib]
  have h1 : (∑ i : Fin 4, minkowskiMetric4 i i *
      (-(1 / 2) * minkowskiDalembertian (fun y => P.traceReversed.h y i i) x))
      = -(1 / 2) * minkowskiDalembertian (fun y => perturbationTrace (P.traceReversed.h y)) x := by
    calc (∑ i : Fin 4, minkowskiMetric4 i i *
          (-(1 / 2) * minkowskiDalembertian (fun y => P.traceReversed.h y i i) x))
        = -(1 / 2) * ∑ i : Fin 4, minkowskiMetric4 i i *
            minkowskiDalembertian (fun y => P.traceReversed.h y i i) x := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun _ _ => by ring
      _ = -(1 / 2) *
            minkowskiDalembertian (fun y => perturbationTrace (P.traceReversed.h y)) x := by
          rw [hbox_trace]
  have h4 : (∑ i : Fin 4, minkowskiMetric4 i i * ((1 / 4) * minkowskiMetric4 i i *
      minkowskiDalembertian (fun y => perturbationTrace (P.traceReversed.h y)) x))
      = minkowskiDalembertian (fun y => perturbationTrace (P.traceReversed.h y)) x := by
    calc (∑ i : Fin 4, minkowskiMetric4 i i * ((1 / 4) * minkowskiMetric4 i i *
          minkowskiDalembertian (fun y => perturbationTrace (P.traceReversed.h y)) x))
        = (1 / 4) * (∑ i : Fin 4, minkowskiMetric4 i i * minkowskiMetric4 i i) *
            minkowskiDalembertian (fun y => perturbationTrace (P.traceReversed.h y)) x := by
          rw [Finset.mul_sum, Finset.sum_mul]; refine Finset.sum_congr rfl fun _ _ => by ring
      _ = minkowskiDalembertian (fun y => perturbationTrace (P.traceReversed.h y)) x := by
          rw [heta_sq]; ring
  rw [h1, h4]
  have h2 : (∑ i : Fin 4, minkowskiMetric4 i i *
      ((1 / 2) * coordDeriv i (fun y => lorenzDivergence P y i) x))
      = (1 / 2) * ∑ a : Fin 4,
          minkowskiMetric4 a a * coordDeriv a (fun y => lorenzDivergence P y a) x := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun _ _ => by ring
  rw [h2]
  ring

/-- Expansion of the linearized Einstein tensor in terms of `□ h̄` and `lorenzDivergence P`:
the trace scalar curvature term cancels identically. -/
lemma linearizedEinstein_in_traceReversed (P : MetricPerturbation) (x : Fin 4 → ℝ)
    (hP : P.IsC2At x) (i j : Fin 4) :
    linearizedEinstein P x i j =
      -(1 / 2) * minkowskiDalembertian (fun y => P.traceReversed.h y i j) x
        + (1 / 2) * coordDeriv i (fun y => lorenzDivergence P y j) x
        + (1 / 2) * coordDeriv j (fun y => lorenzDivergence P y i) x
        - (1 / 2) * minkowskiMetric4 i j * ∑ a : Fin 4,
          minkowskiMetric4 a a * coordDeriv a (fun y => lorenzDivergence P y a) x := by
  simp only [linearizedEinstein, linearizedRicci_in_traceReversed P x hP i j,
    linearizedRicciScalar_in_traceReversed P x hP]
  ring

/-- In Lorenz gauge on a neighborhood of `x`, the linearized Einstein tensor reduces to the wave
equation `G^{(1)}_{ij} = -(1/2) □ h̄_{ij}`. -/
lemma linearizedEinstein_lorenz_gauge (P : MetricPerturbation) (x : Fin 4 → ℝ)
    (hP : P.IsC2At x) (hlz : ∀ᶠ y in nhds x, ∀ k : Fin 4, IsLorenzGauge P y k)
    (i j : Fin 4) :
    linearizedEinstein P x i j =
      -(1 / 2) * minkowskiDalembertian (fun y => P.traceReversed.h y i j) x := by
  have hdiv0 : ∀ μ k, coordDeriv μ (fun y => lorenzDivergence P y k) x = 0 := by
    intro μ k
    have hev : (fun y => lorenzDivergence P y k) =ᶠ[nhds x] fun _ => 0 :=
      hlz.mono fun y hy => hy k
    rw [coordDeriv_congr_nhds μ x hev]
    exact coordDeriv_const μ 0 x
  rw [linearizedEinstein_in_traceReversed P x hP i j]
  simp [hdiv0]

end Linearized

end GeneralRelativity
