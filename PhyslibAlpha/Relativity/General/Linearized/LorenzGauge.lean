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
  ∑ k : Fin 4, minkowskiMetric4 k k * pd k (fun y => traceReversed (h y) k j) x

/-- Lorenz gauge condition `lorenzDiv h x j = 0`. -/
def lorenzGaugeCond (h : (Fin 4 → ℝ) → Tensor2 4) (x : Fin 4 → ℝ) (j : Fin 4) : Prop :=
  lorenzDiv h x j = 0

private lemma linChristoffel_trace (h : (Fin 4 → ℝ) → Tensor2 4) (y : Fin 4 → ℝ)
    (hsym : ∀ z a b, h z a b = h z b a)
    (hh : ∀ a b, DifferentiableAt ℝ (fun z => h z a b) y) (i : Fin 4) :
    (∑ r : Fin 4, linChristoffel h y r r i) = (1 / 2) * pd i (fun z => hTrace (h z)) y := by
  have heq : ∀ r, (fun z => h z r i) = fun z => h z i r := fun r => funext fun z => hsym z r i
  simp only [linChristoffel, heq, add_sub_cancel_right]
  have hsum : (∑ r : Fin 4, (1 / 2) * minkowskiMetric4 r r * pd i (fun z => h z r r) y)
      = (1 / 2) * pd i (fun z => ∑ r : Fin 4, minkowskiMetric4 r r * h z r r) y := by
    rw [pd_sum i (fun r z => minkowskiMetric4 r r * h z r r) y
      (fun r => (slice_differentiableAt i (hh r r)).const_mul _), Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [pd_const_mul, mul_assoc]
  simpa [hTrace] using hsum

private lemma pd_linChristoffel_diag (h : (Fin 4 → ℝ) → Tensor2 4) (x : Fin 4 → ℝ)
    (hsym : ∀ z a b, h z a b = h z b a)
    (hh : ∀ a b, ContDiffAt ℝ 2 (fun z => h z a b) x) (i j : Fin 4) :
    (∑ r : Fin 4, pd j (fun y => linChristoffel h y r r i) x)
      = -(1 / 2) * pd j (pd i (fun z => hTrace (traceReversed (h z)))) x := by
  have nh : ∀ᶠ y in nhds x, ∀ a b, ContDiffAt ℝ 2 (fun z => h z a b) y := by
    rw [Filter.eventually_all]; intro a; rw [Filter.eventually_all]; intro b
    exact (hh a b).eventually (by simp)
  have hdiff_lc : ∀ r, DifferentiableAt ℝ (fun y => linChristoffel h y r r i) x := fun r => by
    simp only [linChristoffel]
    exact (((pd_differentiableAt i (hh r r)).add (pd_differentiableAt r (hh r i))).sub
      (pd_differentiableAt r (hh r i))).const_mul _
  rw [← pd_sum j (fun r y => linChristoffel h y r r i) x
    fun r => slice_differentiableAt j (hdiff_lc r)]
  have hcongr : (fun y => ∑ r : Fin 4, linChristoffel h y r r i) =ᶠ[nhds x]
      fun y => -(1 / 2) * pd i (fun z => hTrace (traceReversed (h z))) y := by
    filter_upwards [nh] with y hy
    rw [linChristoffel_trace h y hsym
      (fun a b => (hy a b).differentiableAt (by norm_num)) i]
    have hT : (fun z => hTrace (h z)) = fun z => -hTrace (traceReversed (h z)) := by
      funext z; simp [traceReversed_trace]
    rw [hT]
    have hdneg : pd i (fun z => -hTrace (traceReversed (h z))) y
        = -pd i (fun z => hTrace (traceReversed (h z))) y := by
      have : (fun z => -hTrace (traceReversed (h z)))
          = fun z => (-1 : ℝ) * hTrace (traceReversed (h z)) := by funext z; ring
      rw [this, pd_const_mul]; ring
    rw [hdneg]
    ring
  rw [pd_congr_nhds j x hcongr, pd_const_mul]

private lemma linChristoffel_eventually_eq_traceReversed (h : (Fin 4 → ℝ) → Tensor2 4)
    (x : Fin 4 → ℝ) (hh : ∀ a b, ContDiffAt ℝ 2 (fun z => h z a b) x) (i j r : Fin 4) :
    (fun y => linChristoffel h y r j i) =ᶠ[nhds x] fun y =>
      (1 / 2) * minkowskiMetric4 r r * (pd i (fun z => traceReversed (h z) r j) y
        + pd j (fun z => traceReversed (h z) r i) y
        - pd r (fun z => traceReversed (h z) j i) y)
        - (1 / 4) * minkowskiMetric4 r r * (minkowskiMetric4 r j *
            pd i (fun z => hTrace (traceReversed (h z))) y
          + minkowskiMetric4 r i * pd j (fun z => hTrace (traceReversed (h z))) y
          - minkowskiMetric4 j i * pd r (fun z => hTrace (traceReversed (h z))) y) := by
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
  rw [pd_sub i y (slice_differentiableAt i (d_b r j))
      ((slice_differentiableAt i d_T).const_mul _),
    pd_sub j y (slice_differentiableAt j (d_b r i))
      ((slice_differentiableAt j d_T).const_mul _),
    pd_sub r y (slice_differentiableAt r (d_b j i))
      ((slice_differentiableAt r d_T).const_mul _),
    pd_const_mul, pd_const_mul, pd_const_mul]
  ring

private lemma pd_linChristoffel_traceReversed (h : (Fin 4 → ℝ) → Tensor2 4) (x : Fin 4 → ℝ)
    (hh : ∀ a b, ContDiffAt ℝ 2 (fun z => h z a b) x) (i j r : Fin 4) :
    pd r (fun y => linChristoffel h y r j i) x =
      (1 / 2) * minkowskiMetric4 r r * pd i (pd r fun z => traceReversed (h z) r j) x
      + (1 / 2) * minkowskiMetric4 r r * pd j (pd r fun z => traceReversed (h z) r i) x
      - (1 / 2) * minkowskiMetric4 r r * pd r (pd r fun z => traceReversed (h z) j i) x
      - (1 / 4) * (minkowskiMetric4 r r * minkowskiMetric4 r j) *
          pd i (pd r fun z => hTrace (traceReversed (h z))) x
      - (1 / 4) * (minkowskiMetric4 r r * minkowskiMetric4 r i) *
          pd j (pd r fun z => hTrace (traceReversed (h z))) x
      + (1 / 4) * minkowskiMetric4 j i *
          (minkowskiMetric4 r r * pd r (pd r fun z => hTrace (traceReversed (h z))) x) := by
  have hb_at : ∀ p q, ContDiffAt ℝ 2 (fun z => traceReversed (h z) p q) x :=
    fun p q => contDiffAt_traceReversed hh p q
  have hT_at : ContDiffAt ℝ 2 (fun z => hTrace (traceReversed (h z))) x :=
    contDiffAt_hTrace hb_at
  have db : ∀ p q μ, DifferentiableAt ℝ (pd μ fun z => traceReversed (h z) p q) x :=
    fun p q μ => pd_differentiableAt μ (hb_at p q)
  have dT : ∀ μ, DifferentiableAt ℝ (pd μ fun z => hTrace (traceReversed (h z))) x :=
    fun μ => pd_differentiableAt μ hT_at
  have h1 : DifferentiableAt ℝ (fun y => (1 / 2 : ℝ) * minkowskiMetric4 r r *
      (pd i (fun z => traceReversed (h z) r j) y
        + pd j (fun z => traceReversed (h z) r i) y
        - pd r (fun z => traceReversed (h z) j i) y)) x :=
    (((db r j i).add (db r i j)).sub (db j i r)).const_mul _
  have h2 : DifferentiableAt ℝ (fun y => (1 / 4 : ℝ) * minkowskiMetric4 r r *
      (minkowskiMetric4 r j * pd i (fun z => hTrace (traceReversed (h z))) y
        + minkowskiMetric4 r i * pd j (fun z => hTrace (traceReversed (h z))) y
        - minkowskiMetric4 j i * pd r (fun z => hTrace (traceReversed (h z))) y)) x :=
    ((((dT i).const_mul _).add ((dT j).const_mul _)).sub ((dT r).const_mul _)).const_mul _
  have d1 : DifferentiableAt ℝ
      (fun s => pd i (fun z => traceReversed (h z) r j) (Function.update x r s)) (x r) :=
    slice_differentiableAt r (db r j i)
  have d2 : DifferentiableAt ℝ
      (fun s => pd j (fun z => traceReversed (h z) r i) (Function.update x r s)) (x r) :=
    slice_differentiableAt r (db r i j)
  have d3 : DifferentiableAt ℝ
      (fun s => pd r (fun z => traceReversed (h z) j i) (Function.update x r s)) (x r) :=
    slice_differentiableAt r (db j i r)
  have dt1 : DifferentiableAt ℝ (fun s => minkowskiMetric4 r j *
      pd i (fun z => hTrace (traceReversed (h z))) (Function.update x r s)) (x r) :=
    (slice_differentiableAt r (dT i)).const_mul _
  have dt2 : DifferentiableAt ℝ (fun s => minkowskiMetric4 r i *
      pd j (fun z => hTrace (traceReversed (h z))) (Function.update x r s)) (x r) :=
    (slice_differentiableAt r (dT j)).const_mul _
  have dt3 : DifferentiableAt ℝ (fun s => minkowskiMetric4 j i *
      pd r (fun z => hTrace (traceReversed (h z))) (Function.update x r s)) (x r) :=
    (slice_differentiableAt r (dT r)).const_mul _
  rw [pd_congr_nhds r x (linChristoffel_eventually_eq_traceReversed h x hh i j r),
    pd_sub r x (slice_differentiableAt r h1) (slice_differentiableAt r h2),
    pd_const_mul, pd_const_mul,
    pd_sub r x (d1.add d2) d3, pd_add r x d1 d2,
    pd_sub r x (dt1.add dt2) dt3, pd_add r x dt1 dt2,
    pd_const_mul, pd_const_mul, pd_const_mul,
    pd_comm r i (hb_at r j), pd_comm r j (hb_at r i), pd_comm r i hT_at, pd_comm r j hT_at]
  ring

private lemma pd_lorenzDiv (h : (Fin 4 → ℝ) → Tensor2 4) (x : Fin 4 → ℝ)
    (hh : ∀ a b, ContDiffAt ℝ 2 (fun z => h z a b) x) (i j : Fin 4) :
    pd i (fun y => lorenzDiv h y j) x
      = ∑ r : Fin 4, minkowskiMetric4 r r * pd i (pd r fun z => traceReversed (h z) r j) x := by
  simp only [lorenzDiv]
  rw [pd_sum i _ x fun r =>
    slice_differentiableAt i
      ((pd_differentiableAt r (contDiffAt_traceReversed hh r j)).const_mul _)]
  refine Finset.sum_congr rfl fun r _ => pd_const_mul i (minkowskiMetric4 r r) x

/-- Expansion of `linRicci h x i j` in terms of `h̄ = traceReversed h` and `lorenzDiv h`. -/
lemma linRicci_in_traceReversed (h : (Fin 4 → ℝ) → Tensor2 4) (x : Fin 4 → ℝ)
    (hsym : ∀ z a b, h z a b = h z b a)
    (hh : ∀ a b, ContDiffAt ℝ 2 (fun z => h z a b) x) (i j : Fin 4) :
    linRicci h x i j = -(1 / 2) * boxEta (fun y => traceReversed (h y) i j) x
      + (1 / 2) * pd i (fun y => lorenzDiv h y j) x
      + (1 / 2) * pd j (fun y => lorenzDiv h y i) x
      + (1 / 4) * minkowskiMetric4 i j * boxEta (fun y => hTrace (traceReversed (h y))) x := by
  have hT_at : ContDiffAt ℝ 2 (fun z => hTrace (traceReversed (h z))) x :=
    contDiffAt_hTrace fun p q => contDiffAt_traceReversed hh p q
  have hdiv_j := pd_lorenzDiv h x hh i j
  have hdiv_i := pd_lorenzDiv h x hh j i
  have hbox_sym : boxEta (fun y => traceReversed (h y) j i) x =
      boxEta (fun y => traceReversed (h y) i j) x := by
    have hbs : (fun y => traceReversed (h y) j i) = fun y => traceReversed (h y) i j :=
      funext fun y =>
        (traceReversed_symm
          (show IsSymm (h y) from Matrix.IsSymm.ext fun a b => hsym y b a)).apply i j
    simp [hbs]
  have hT_sub_j : (∑ r : Fin 4, (1 / 4 : ℝ) * (minkowskiMetric4 r r * minkowskiMetric4 r j) *
      pd i (pd r fun z => hTrace (traceReversed (h z))) x)
      = (1 / 4) * pd i (pd j fun z => hTrace (traceReversed (h z))) x := by
    fin_cases j <;> simp
  have hT_sub_i : (∑ r : Fin 4, (1 / 4 : ℝ) * (minkowskiMetric4 r r * minkowskiMetric4 r i) *
      pd j (pd r fun z => hTrace (traceReversed (h z))) x)
      = (1 / 4) * pd j (pd i fun z => hTrace (traceReversed (h z))) x := by
    fin_cases i <;> simp
  have hT_comm : pd j (pd i fun z => hTrace (traceReversed (h z))) x =
      pd i (pd j fun z => hTrace (traceReversed (h z))) x := pd_comm j i hT_at
  simp only [linRicci, linRiemann, Finset.sum_sub_distrib, pd_linChristoffel_traceReversed h x hh,
    pd_linChristoffel_diag h x hsym hh i j, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [hdiv_j, hdiv_i, ← hbox_sym, minkowskiMetric4_symm.apply i j, hT_sub_j, hT_sub_i, hT_comm]
  have hs1 : (∑ r : Fin 4, (1 / 2 : ℝ) * minkowskiMetric4 r r *
      pd i (pd r fun z => traceReversed (h z) r j) x)
      = (1 / 2) * ∑ r : Fin 4, minkowskiMetric4 r r *
        pd i (pd r fun z => traceReversed (h z) r j) x := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun _ _ => by ring
  have hs2 : (∑ r : Fin 4, (1 / 2 : ℝ) * minkowskiMetric4 r r *
      pd j (pd r fun z => traceReversed (h z) r i) x)
      = (1 / 2) * ∑ r : Fin 4, minkowskiMetric4 r r *
        pd j (pd r fun z => traceReversed (h z) r i) x := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun _ _ => by ring
  have hs3 : (∑ r : Fin 4, (1 / 2 : ℝ) * minkowskiMetric4 r r *
      pd r (pd r fun z => traceReversed (h z) j i) x)
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
  have hdμ : ∀ i, DifferentiableAt ℝ (pd μ fun y => b y i i) x :=
    fun i => pd_differentiableAt μ (hb i i)
  have hcongr :
      (fun y => ∑ i : Fin 4, minkowskiMetric4 i i * b y i i) = fun y => hTrace (b y) :=
    funext fun y => (metricTrace_minkowski (b y)).symm
  have hpd1 : ∀ y, (∀ i, DifferentiableAt ℝ (fun z => b z i i) y) →
      pd μ (fun z => hTrace (b z)) y =
        ∑ i : Fin 4, minkowskiMetric4 i i * pd μ (fun z => b z i i) y := by
    intro y hy
    rw [← hcongr, pd_sum μ _ y fun i => (slice_differentiableAt μ (hy i)).const_mul _]
    refine Finset.sum_congr rfl fun i _ => pd_const_mul μ (minkowskiMetric4 i i) y
  have nh : ∀ᶠ y in nhds x, ∀ a b', ContDiffAt ℝ 2 (fun z => b z a b') y := by
    rw [Filter.eventually_all]; intro a; rw [Filter.eventually_all]; intro b'
    exact (hb a b').eventually (by simp)
  have hev : pd μ (fun z => hTrace (b z)) =ᶠ[nhds x] fun y =>
      ∑ i : Fin 4, minkowskiMetric4 i i * pd μ (fun z => b z i i) y := by
    filter_upwards [nh] with y hy
    exact hpd1 y fun i => (hy i i).differentiableAt (by norm_num)
  rw [pd_congr_nhds μ x hev,
    pd_sum μ _ x fun i => slice_differentiableAt μ ((hdμ i).const_mul _),
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [pd_const_mul, mul_left_comm]

private lemma linScalar_in_traceReversed (h : (Fin 4 → ℝ) → Tensor2 4) (x : Fin 4 → ℝ)
    (hsym : ∀ z a b, h z a b = h z b a)
    (hh : ∀ a b, ContDiffAt ℝ 2 (fun z => h z a b) x) :
    linScalar h x = (1 / 2) * boxEta (fun y => hTrace (traceReversed (h y))) x
      + ∑ a : Fin 4, minkowskiMetric4 a a * pd a (fun y => lorenzDiv h y a) x := by
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
  have h2 : (∑ i : Fin 4, minkowskiMetric4 i i * ((1 / 2) * pd i (fun y => lorenzDiv h y i) x))
      = (1 / 2) * ∑ a : Fin 4, minkowskiMetric4 a a * pd a (fun y => lorenzDiv h y a) x := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun _ _ => by ring
  rw [h2]
  ring

/-- Expansion of the linearized Einstein tensor in terms of `□ h̄` and `lorenzDiv h`:
the trace scalar curvature term cancels identically. -/
lemma linEinstein_in_traceReversed (h : (Fin 4 → ℝ) → Tensor2 4) (x : Fin 4 → ℝ)
    (hsym : ∀ z a b, h z a b = h z b a)
    (hh : ∀ a b, ContDiffAt ℝ 2 (fun z => h z a b) x) (i j : Fin 4) :
    linEinstein h x i j = -(1 / 2) * boxEta (fun y => traceReversed (h y) i j) x
      + (1 / 2) * pd i (fun y => lorenzDiv h y j) x
      + (1 / 2) * pd j (fun y => lorenzDiv h y i) x
      - (1 / 2) * minkowskiMetric4 i j * ∑ a : Fin 4,
        minkowskiMetric4 a a * pd a (fun y => lorenzDiv h y a) x := by
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
  have hdiv0 : ∀ μ k, pd μ (fun y => lorenzDiv h y k) x = 0 := by
    intro μ k
    have hev : (fun y => lorenzDiv h y k) =ᶠ[nhds x] fun _ => 0 :=
      hlz.mono fun y hy => hy k
    rw [pd_congr_nhds μ x hev]
    exact pd_const μ 0 x
  rw [linEinstein_in_traceReversed h x hsym hh i j]
  simp [hdiv0]

end Linearized

end GeneralRelativity
