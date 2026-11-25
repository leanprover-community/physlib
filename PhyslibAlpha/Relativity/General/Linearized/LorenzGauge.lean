/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import PhyslibAlpha.Relativity.General.Linearized.LinearizedCurvature
import Mathlib.Tactic.Ring

/-!

# Lorenz gauge and linearized wave equation

The Lorenz (harmonic/de Donder) gauge condition `∂^k h̄_{kj} = 0` and reduction of the linearized
Einstein tensor to `-(1/2) □_η h̄_{ij}`.

## i. Overview

Expressing the linearized Ricci tensor and Ricci scalar in terms of the trace-reversed
perturbation `h̄ = traceReversed h` and the Lorenz gauge divergence `lorenzDiv h`, the scalar
wave term cancels in the linearized Einstein tensor `linEinstein`. Consequently, whenever
`lorenzGaugeCond h` holds on a neighborhood of `x`, `linEinstein` reduces to the flat-space
wave operator `-(1/2) □_η h̄_{ij}`.

## ii. Key results

- `lorenzDiv`, `lorenzGaugeCond` : Lorenz gauge divergence vector and vanishing condition.
- `linRicci_in_traceReversed`, `linEinstein_in_traceReversed` : expansion in `h̄` and
  `lorenzDiv`.
- `linEinstein_lorenz_gauge` : Lorenz-gauge wave equation `linEinstein = -(1/2) □_η h̄`.

## iii. Table of contents

- A. Lorenz gauge and wave equation reduction

## iv. References

* R. M. Wald, *General Relativity* (1984). [ref: wald_1984_general_relativity]
* C. W. Misner, K. S. Thorne, and J. A. Wheeler, *Gravitation* (1973). [ref: mtw_1973_gravitation]

-/

@[expose] public section

namespace GeneralRelativity

namespace Linearized

open Pipeline

/-!

## A. Lorenz gauge and wave equation reduction

Using Schwarz symmetry `∂_μ ∂_ν = ∂_ν ∂_μ` on the second derivatives of `h̄` cancels the mixed
cross terms and scalar trace, reducing `linEinstein` in Lorenz gauge `∂^k h̄_{kj} = 0` to the
flat-space gravitational wave operator `-(1/2) □_η h̄_{ij}`.

-/

/-- Lorenz (harmonic/de Donder) gauge divergence vector `∂^k h̄_{kj} = η^{kk} ∂_k h̄_{kj}`. -/
noncomputable def lorenzDiv (h : (Fin 4 → ℝ) → Tensor2 4) (x : Fin 4 → ℝ) (j : Fin 4) : ℝ :=
  ∑ k : Fin 4, minkowskiMetric4 k k * coordDeriv k (fun y => traceReversed (h y) k j) x

/-- Lorenz gauge condition `lorenzDiv h x j = 0`. -/
def lorenzGaugeCond (h : (Fin 4 → ℝ) → Tensor2 4) (x : Fin 4 → ℝ) (j : Fin 4) : Prop :=
  lorenzDiv h x j = 0

private lemma linChristoffel_trace (h : (Fin 4 → ℝ) → Tensor2 4) (y : Fin 4 → ℝ)
    (hsym : ∀ z a b, h z a b = h z b a)
    (hh : ∀ a b, DifferentiableAt ℝ (fun z => h z a b) y) (i : Fin 4) :
    (∑ r : Fin 4, linChristoffel h y r r i) = (1 / 2) * coordDeriv i (fun z => hTrace (h z)) y := by
  have heq : ∀ r, (fun z => h z r i) = fun z => h z i r := fun r => funext fun z => hsym z r i
  simp only [linChristoffel, heq, add_sub_cancel_right]
  have hsum : (∑ r : Fin 4, (1 / 2) * minkowskiMetric4 r r * coordDeriv i (fun z => h z r r) y)
      = (1 / 2) * coordDeriv i (fun z => ∑ r : Fin 4, minkowskiMetric4 r r * h z r r) y := by
    rw [coordDeriv_sum i (fun r z => minkowskiMetric4 r r * h z r r) y
      (fun r => (slice_differentiableAt i (hh r r)).const_mul _), Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [coordDeriv_const_mul, mul_assoc]
  simpa [hTrace] using hsum

private lemma pd_linChristoffel_diag (h : (Fin 4 → ℝ) → Tensor2 4) (x : Fin 4 → ℝ)
    (hsym : ∀ z a b, h z a b = h z b a)
    (hh : ∀ a b, ContDiffAt ℝ 2 (fun z => h z a b) x) (i j : Fin 4) :
    (∑ r : Fin 4, coordDeriv j (fun y => linChristoffel h y r r i) x)
      = -(1 / 2) * coordDeriv j (coordDeriv i (fun z => hTrace (traceReversed (h z)))) x := by
  have nh : ∀ᶠ y in nhds x, ∀ a b, ContDiffAt ℝ 2 (fun z => h z a b) y := by
    rw [Filter.eventually_all]; intro a; rw [Filter.eventually_all]; intro b
    exact (hh a b).eventually (by simp)
  have hdiff_lc : ∀ r, DifferentiableAt ℝ (fun y => linChristoffel h y r r i) x := fun r => by
    simp only [linChristoffel]
    exact (((coordDeriv_differentiableAt i (hh r r)).add
      (coordDeriv_differentiableAt r (hh r i))).sub
      (coordDeriv_differentiableAt r (hh r i))).const_mul _
  rw [← coordDeriv_sum j (fun r y => linChristoffel h y r r i) x
    fun r => slice_differentiableAt j (hdiff_lc r)]
  have hcongr : (fun y => ∑ r : Fin 4, linChristoffel h y r r i) =ᶠ[nhds x]
      fun y => -(1 / 2) * coordDeriv i (fun z => hTrace (traceReversed (h z))) y := by
    filter_upwards [nh] with y hy
    rw [linChristoffel_trace h y hsym
      (fun a b => (hy a b).differentiableAt (by norm_num)) i]
    have hT : (fun z => hTrace (h z)) = fun z => -hTrace (traceReversed (h z)) := by
      funext z; simp [traceReversed_trace]
    rw [hT]
    have hdneg : coordDeriv i (fun z => -hTrace (traceReversed (h z))) y
        = -coordDeriv i (fun z => hTrace (traceReversed (h z))) y := by
      have : (fun z => -hTrace (traceReversed (h z)))
          = fun z => (-1 : ℝ) * hTrace (traceReversed (h z)) := by funext z; ring
      rw [this, coordDeriv_const_mul]; ring
    rw [hdneg]
    ring
  rw [coordDeriv_congr_nhds j x hcongr, coordDeriv_const_mul]

private lemma linChristoffel_eventually_eq_traceReversed (h : (Fin 4 → ℝ) → Tensor2 4)
    (x : Fin 4 → ℝ) (hh : ∀ a b, ContDiffAt ℝ 2 (fun z => h z a b) x) (i j r : Fin 4) :
    (fun y => linChristoffel h y r j i) =ᶠ[nhds x] fun y =>
      (1 / 2) * minkowskiMetric4 r r * (coordDeriv i (fun z => traceReversed (h z) r j) y
        + coordDeriv j (fun z => traceReversed (h z) r i) y
        - coordDeriv r (fun z => traceReversed (h z) j i) y)
        - (1 / 4) * minkowskiMetric4 r r * (minkowskiMetric4 r j *
            coordDeriv i (fun z => hTrace (traceReversed (h z))) y
          + minkowskiMetric4 r i * coordDeriv j (fun z => hTrace (traceReversed (h z))) y
          - minkowskiMetric4 j i * coordDeriv r (fun z => hTrace (traceReversed (h z))) y) := by
  have nh : ∀ᶠ y in nhds x, ∀ a b', ContDiffAt ℝ 2 (fun z => h z a b') y := by
    rw [Filter.eventually_all]; intro a; rw [Filter.eventually_all]; intro b'
    exact (hh a b').eventually (by simp)
  filter_upwards [nh] with y hy
  have hb_c2 : ∀ p q, ContDiffAt ℝ 2 (fun z => traceReversed (h z) p q) y :=
    fun p q => contDiffAt_traceReversed hy p q
  have hT_c2 : ContDiffAt ℝ 2 (fun z => hTrace (traceReversed (h z))) y :=
    contDiffAt_hTrace hb_c2
  have hcd : ∀ p q, (fun z => h z p q) = fun z =>
      traceReversed (h z) p q
        - (1 / 2) * minkowskiMetric4 p q * hTrace (traceReversed (h z)) := by
    intro p q; funext z
    have hi := congrArg (fun M => M p q) (traceReversed_involutive (h z))
    simpa [traceReversed] using hi.symm
  have d_b : ∀ p q, DifferentiableAt ℝ (fun z => traceReversed (h z) p q) y :=
    fun p q => (hb_c2 p q).differentiableAt (by norm_num)
  have d_T : DifferentiableAt ℝ (fun z => hTrace (traceReversed (h z))) y :=
    hT_c2.differentiableAt (by norm_num)
  simp only [linChristoffel, hcd]
  rw [coordDeriv_sub i y (slice_differentiableAt i (d_b r j))
      ((slice_differentiableAt i d_T).const_mul _),
    coordDeriv_sub j y (slice_differentiableAt j (d_b r i))
      ((slice_differentiableAt j d_T).const_mul _),
    coordDeriv_sub r y (slice_differentiableAt r (d_b j i))
      ((slice_differentiableAt r d_T).const_mul _),
    coordDeriv_const_mul, coordDeriv_const_mul, coordDeriv_const_mul]
  ring

private lemma coordDeriv_traceReversed_differentiableAt (h : (Fin 4 → ℝ) → Tensor2 4)
    (x : Fin 4 → ℝ) (hh : ∀ a b, ContDiffAt ℝ 2 (fun z => h z a b) x) (p q μ : Fin 4) :
    DifferentiableAt ℝ (coordDeriv μ fun z => traceReversed (h z) p q) x :=
  coordDeriv_differentiableAt μ (contDiffAt_traceReversed hh p q)

private lemma coordDeriv_hTrace_traceReversed_differentiableAt (h : (Fin 4 → ℝ) → Tensor2 4)
    (x : Fin 4 → ℝ) (hh : ∀ a b, ContDiffAt ℝ 2 (fun z => h z a b) x) (μ : Fin 4) :
    DifferentiableAt ℝ (coordDeriv μ fun z => hTrace (traceReversed (h z))) x :=
  coordDeriv_differentiableAt μ (contDiffAt_hTrace fun p q => contDiffAt_traceReversed hh p q)

private lemma sum_eta_diag_mul_coordDeriv_hTrace (h : (Fin 4 → ℝ) → Tensor2 4) (x : Fin 4 → ℝ)
    (k l : Fin 4) :
    (∑ r : Fin 4, (1 / 4 : ℝ) * (minkowskiMetric4 r r * minkowskiMetric4 r k) *
      coordDeriv l (coordDeriv r fun z => hTrace (traceReversed (h z))) x)
      = (1 / 4) * coordDeriv l (coordDeriv k fun z => hTrace (traceReversed (h z))) x := by
  fin_cases k <;> simp

private lemma pd_linChristoffel_traceReversed (h : (Fin 4 → ℝ) → Tensor2 4) (x : Fin 4 → ℝ)
    (hh : ∀ a b, ContDiffAt ℝ 2 (fun z => h z a b) x) (i j r : Fin 4) :
    coordDeriv r (fun y => linChristoffel h y r j i) x =
      (1 / 2) * minkowskiMetric4 r r *
        coordDeriv i (coordDeriv r fun z => traceReversed (h z) r j) x
      + (1 / 2) * minkowskiMetric4 r r *
        coordDeriv j (coordDeriv r fun z => traceReversed (h z) r i) x
      - (1 / 2) * minkowskiMetric4 r r *
        coordDeriv r (coordDeriv r fun z => traceReversed (h z) j i) x
      - (1 / 4) * (minkowskiMetric4 r r * minkowskiMetric4 r j) *
          coordDeriv i (coordDeriv r fun z => hTrace (traceReversed (h z))) x
      - (1 / 4) * (minkowskiMetric4 r r * minkowskiMetric4 r i) *
          coordDeriv j (coordDeriv r fun z => hTrace (traceReversed (h z))) x
      + (1 / 4) * minkowskiMetric4 j i *
          (minkowskiMetric4 r r *
            coordDeriv r (coordDeriv r fun z => hTrace (traceReversed (h z))) x) := by
  have hb := fun p q => contDiffAt_traceReversed hh p q
  have hT := contDiffAt_hTrace hb
  have db := coordDeriv_traceReversed_differentiableAt h x hh
  have dT := coordDeriv_hTrace_traceReversed_differentiableAt h x hh
  have h1 : DifferentiableAt ℝ (fun y => (1 / 2 : ℝ) * minkowskiMetric4 r r *
      (coordDeriv i (fun z => traceReversed (h z) r j) y
        + coordDeriv j (fun z => traceReversed (h z) r i) y
        - coordDeriv r (fun z => traceReversed (h z) j i) y)) x :=
    (((db r j i).add (db r i j)).sub (db j i r)).const_mul _
  have h2 : DifferentiableAt ℝ (fun y => (1 / 4 : ℝ) * minkowskiMetric4 r r *
      (minkowskiMetric4 r j * coordDeriv i (fun z => hTrace (traceReversed (h z))) y
        + minkowskiMetric4 r i * coordDeriv j (fun z => hTrace (traceReversed (h z))) y
        - minkowskiMetric4 j i * coordDeriv r (fun z => hTrace (traceReversed (h z))) y)) x :=
    ((((dT i).const_mul _).add ((dT j).const_mul _)).sub ((dT r).const_mul _)).const_mul _
  rw [coordDeriv_congr_nhds r x (linChristoffel_eventually_eq_traceReversed h x hh i j r),
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

private lemma pd_lorenzDiv (h : (Fin 4 → ℝ) → Tensor2 4) (x : Fin 4 → ℝ)
    (hh : ∀ a b, ContDiffAt ℝ 2 (fun z => h z a b) x) (i j : Fin 4) :
    coordDeriv i (fun y => lorenzDiv h y j) x = ∑ r : Fin 4,
      minkowskiMetric4 r r * coordDeriv i (coordDeriv r fun z => traceReversed (h z) r j) x := by
  simp only [lorenzDiv]
  rw [coordDeriv_sum i _ x fun r =>
    slice_differentiableAt i
      ((coordDeriv_differentiableAt r (contDiffAt_traceReversed hh r j)).const_mul _)]
  refine Finset.sum_congr rfl fun r _ => coordDeriv_const_mul i (minkowskiMetric4 r r) x

/-- Expansion of `linRicci h x i j` in terms of `h̄ = traceReversed h` and `lorenzDiv h`. -/
lemma linRicci_in_traceReversed (h : (Fin 4 → ℝ) → Tensor2 4) (x : Fin 4 → ℝ)
    (hsym : ∀ z a b, h z a b = h z b a)
    (hh : ∀ a b, ContDiffAt ℝ 2 (fun z => h z a b) x) (i j : Fin 4) :
    linRicci h x i j = -(1 / 2) * boxEta (fun y => traceReversed (h y) i j) x
      + (1 / 2) * coordDeriv i (fun y => lorenzDiv h y j) x
      + (1 / 2) * coordDeriv j (fun y => lorenzDiv h y i) x
      + (1 / 4) * minkowskiMetric4 i j * boxEta (fun y => hTrace (traceReversed (h y))) x := by
  have hT := contDiffAt_hTrace fun p q => contDiffAt_traceReversed hh p q
  have hbox_sym : boxEta (fun y => traceReversed (h y) j i) x =
      boxEta (fun y => traceReversed (h y) i j) x := by
    have hbs : (fun y => traceReversed (h y) j i) = fun y => traceReversed (h y) i j :=
      funext fun y =>
        (traceReversed_symm
          (show IsSymm (h y) from Matrix.IsSymm.ext fun a b => hsym y b a)).apply i j
    simp [hbs]
  simp only [linRicci, linRiemann, Finset.sum_sub_distrib, pd_linChristoffel_traceReversed h x hh,
    pd_linChristoffel_diag h x hsym hh i j, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [pd_lorenzDiv h x hh i j, pd_lorenzDiv h x hh j i, ← hbox_sym,
    minkowskiMetric4_symm.apply i j,
    sum_eta_diag_mul_coordDeriv_hTrace h x j i, sum_eta_diag_mul_coordDeriv_hTrace h x i j,
    coordDeriv_comm j i hT]
  have hs1 : (∑ r : Fin 4, (1 / 2 : ℝ) * minkowskiMetric4 r r *
      coordDeriv i (coordDeriv r fun z => traceReversed (h z) r j) x)
      = (1 / 2) * ∑ r : Fin 4, minkowskiMetric4 r r *
        coordDeriv i (coordDeriv r fun z => traceReversed (h z) r j) x := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun _ _ => by ring
  have hs2 : (∑ r : Fin 4, (1 / 2 : ℝ) * minkowskiMetric4 r r *
      coordDeriv j (coordDeriv r fun z => traceReversed (h z) r i) x)
      = (1 / 2) * ∑ r : Fin 4, minkowskiMetric4 r r *
        coordDeriv j (coordDeriv r fun z => traceReversed (h z) r i) x := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun _ _ => by ring
  have hs3 : (∑ r : Fin 4, (1 / 2 : ℝ) * minkowskiMetric4 r r *
      coordDeriv r (coordDeriv r fun z => traceReversed (h z) j i) x)
      = (1 / 2) * boxEta (fun y => traceReversed (h y) j i) x := by
    simp only [boxEta, Finset.mul_sum]
    refine Finset.sum_congr rfl fun _ _ => by ring
  rw [hs1, hs2, hs3]
  simp only [boxEta]
  ring

private lemma boxEta_hTrace (b : (Fin 4 → ℝ) → Tensor2 4) (x : Fin 4 → ℝ)
    (hb : ∀ a b', ContDiffAt ℝ 2 (fun z => b z a b') x) :
    (∑ i : Fin 4, minkowskiMetric4 i i * boxEta (fun y => b y i i) x) =
      boxEta (fun y => hTrace (b y)) x := by
  simp only [boxEta, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun μ _ => ?_
  have hdμ : ∀ i, DifferentiableAt ℝ (coordDeriv μ fun y => b y i i) x :=
    fun i => coordDeriv_differentiableAt μ (hb i i)
  have hcongr :
      (fun y => ∑ i : Fin 4, minkowskiMetric4 i i * b y i i) = fun y => hTrace (b y) :=
    funext fun y => (metricTrace_minkowski (b y)).symm
  have hpd1 : ∀ y, (∀ i, DifferentiableAt ℝ (fun z => b z i i) y) →
      coordDeriv μ (fun z => hTrace (b z)) y =
        ∑ i : Fin 4, minkowskiMetric4 i i * coordDeriv μ (fun z => b z i i) y := by
    intro y hy
    rw [← hcongr, coordDeriv_sum μ _ y fun i => (slice_differentiableAt μ (hy i)).const_mul _]
    refine Finset.sum_congr rfl fun i _ => coordDeriv_const_mul μ (minkowskiMetric4 i i) y
  have nh : ∀ᶠ y in nhds x, ∀ a b', ContDiffAt ℝ 2 (fun z => b z a b') y := by
    rw [Filter.eventually_all]; intro a; rw [Filter.eventually_all]; intro b'
    exact (hb a b').eventually (by simp)
  have hev : coordDeriv μ (fun z => hTrace (b z)) =ᶠ[nhds x] fun y =>
      ∑ i : Fin 4, minkowskiMetric4 i i * coordDeriv μ (fun z => b z i i) y := by
    filter_upwards [nh] with y hy
    exact hpd1 y fun i => (hy i i).differentiableAt (by norm_num)
  rw [coordDeriv_congr_nhds μ x hev,
    coordDeriv_sum μ _ x fun i => slice_differentiableAt μ ((hdμ i).const_mul _),
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [coordDeriv_const_mul, mul_left_comm]

private lemma linScalar_in_traceReversed (h : (Fin 4 → ℝ) → Tensor2 4) (x : Fin 4 → ℝ)
    (hsym : ∀ z a b, h z a b = h z b a)
    (hh : ∀ a b, ContDiffAt ℝ 2 (fun z => h z a b) x) :
    linScalar h x = (1 / 2) * boxEta (fun y => hTrace (traceReversed (h y))) x
      + ∑ a : Fin 4, minkowskiMetric4 a a * coordDeriv a (fun y => lorenzDiv h y a) x := by
  have hb_at : ∀ p q, ContDiffAt ℝ 2 (fun z => traceReversed (h z) p q) x := fun p q =>
    contDiffAt_traceReversed hh p q
  have hbox_trace := boxEta_hTrace (fun z => traceReversed (h z)) x hb_at
  have heta_sq : (∑ i : Fin 4, minkowskiMetric4 i i * minkowskiMetric4 i i) = 4 := by
    simp [Fin.sum_univ_four]
    norm_num
  simp only [linScalar, linRicci_in_traceReversed h x hsym hh, mul_add,
    Finset.sum_add_distrib]
  have h1 : (∑ i : Fin 4, minkowskiMetric4 i i *
      (-(1 / 2) * boxEta (fun y => traceReversed (h y) i i) x))
      = -(1 / 2) * boxEta (fun y => hTrace (traceReversed (h y))) x := by
    calc (∑ i : Fin 4, minkowskiMetric4 i i *
          (-(1 / 2) * boxEta (fun y => traceReversed (h y) i i) x))
        = -(1 / 2) * ∑ i : Fin 4,
            minkowskiMetric4 i i * boxEta (fun y => traceReversed (h y) i i) x := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun _ _ => by ring
      _ = -(1 / 2) * boxEta (fun y => hTrace (traceReversed (h y))) x := by rw [hbox_trace]
  have h4 : (∑ i : Fin 4, minkowskiMetric4 i i *
      ((1 / 4) * minkowskiMetric4 i i * boxEta (fun y => hTrace (traceReversed (h y))) x))
      = boxEta (fun y => hTrace (traceReversed (h y))) x := by
    calc (∑ i : Fin 4, minkowskiMetric4 i i * ((1 / 4) * minkowskiMetric4 i i *
          boxEta (fun y => hTrace (traceReversed (h y))) x))
        = (1 / 4) * (∑ i : Fin 4, minkowskiMetric4 i i * minkowskiMetric4 i i) *
            boxEta (fun y => hTrace (traceReversed (h y))) x := by
          rw [Finset.mul_sum, Finset.sum_mul]; refine Finset.sum_congr rfl fun _ _ => by ring
      _ = boxEta (fun y => hTrace (traceReversed (h y))) x := by rw [heta_sq]; ring
  rw [h1, h4]
  have h2 : (∑ i : Fin 4, minkowskiMetric4 i i *
      ((1 / 2) * coordDeriv i (fun y => lorenzDiv h y i) x))
      = (1 / 2) * ∑ a : Fin 4,
          minkowskiMetric4 a a * coordDeriv a (fun y => lorenzDiv h y a) x := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun _ _ => by ring
  rw [h2]
  ring

/-- Expansion of the linearized Einstein tensor in terms of `□ h̄` and `lorenzDiv h`:
the trace scalar curvature term cancels identically. -/
lemma linEinstein_in_traceReversed (h : (Fin 4 → ℝ) → Tensor2 4) (x : Fin 4 → ℝ)
    (hsym : ∀ z a b, h z a b = h z b a)
    (hh : ∀ a b, ContDiffAt ℝ 2 (fun z => h z a b) x) (i j : Fin 4) :
    linEinstein h x i j = -(1 / 2) * boxEta (fun y => traceReversed (h y) i j) x
      + (1 / 2) * coordDeriv i (fun y => lorenzDiv h y j) x
      + (1 / 2) * coordDeriv j (fun y => lorenzDiv h y i) x
      - (1 / 2) * minkowskiMetric4 i j * ∑ a : Fin 4,
        minkowskiMetric4 a a * coordDeriv a (fun y => lorenzDiv h y a) x := by
  simp only [linEinstein, linRicci_in_traceReversed h x hsym hh i j,
    linScalar_in_traceReversed h x hsym hh]
  ring

/-- In Lorenz gauge on a neighborhood of `x`, the linearized Einstein tensor reduces to the wave
equation `G^{(1)}_{ij} = -(1/2) □ h̄_{ij}`. -/
lemma linEinstein_lorenz_gauge (h : (Fin 4 → ℝ) → Tensor2 4) (x : Fin 4 → ℝ)
    (hsym : ∀ z a b, h z a b = h z b a)
    (hh : ∀ a b, ContDiffAt ℝ 2 (fun z => h z a b) x)
    (hlz : ∀ᶠ y in nhds x, ∀ k : Fin 4, lorenzGaugeCond h y k) (i j : Fin 4) :
    linEinstein h x i j = -(1 / 2) * boxEta (fun y => traceReversed (h y) i j) x := by
  have hdiv0 : ∀ μ k, coordDeriv μ (fun y => lorenzDiv h y k) x = 0 := by
    intro μ k
    have hev : (fun y => lorenzDiv h y k) =ᶠ[nhds x] fun _ => 0 :=
      hlz.mono fun y hy => hy k
    rw [coordDeriv_congr_nhds μ x hev]
    exact coordDeriv_const μ 0 x
  rw [linEinstein_in_traceReversed h x hsym hh i j]
  simp [hdiv0]

end Linearized

end GeneralRelativity
