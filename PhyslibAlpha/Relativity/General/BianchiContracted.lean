/-
Copyright (c) 2026 Alex Vergara Gil.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import PhyslibAlpha.Relativity.General.Bianchi

/-!
# The contracted Bianchi identity and Einstein tensor conservation

The contraction of the second Bianchi identity, and the resulting conservation
law for the Einstein tensor.

## i. Overview

Contracting the second Bianchi identity once with the inverse metric gives the
contracted Bianchi identity `∇^μ Ric_{μλ} = ½ ∂_λ S`.  Contracting it a second
time gives `∇^μ G_{μλ} = 0`: the Einstein tensor is divergence free
identically, which is why `G_{μν} + Λ g_{μν}` is the only conserved second-order
combination of the metric and its derivatives.  The proof sums the second
Bianchi identity over the free indices, moves the inverse metric through the
coordinate derivatives, and identifies the surviving terms with the derivative
of the Ricci scalar.

## ii. Key results

- `differentiableAt_riemann` : the Riemann tensor is differentiable when the
  Christoffel symbols are `C²`.

- `contracted_bianchi` : `∇^μ Ric_{μλ} = ½ ∂_λ S`.
- `covDiv_einstein_eq_zero` : `∇^μ G_{μλ} = 0`.

## iii. Table of contents

- A. The contracted identity

## iv. References

* S. M. Carroll, *Lecture Notes on General Relativity*, arXiv:gr-qc/9712019,
  §3.2, pp. 72–73. [ref: Carroll1997]

-/

@[expose] public section

namespace GeneralRelativity

namespace Bianchi

open CoordinateCurvature Topology Filter

/-! ## A. The contracted identity -/

/-- Differentiability of `riemann` from `C²` Christoffel symbols. -/
lemma differentiableAt_riemann {n : ℕ} (g ginv : (Fin n → ℝ) → Tensor2 n) {x : Fin n → ℝ}
    (hΓC2 : ∀ k i j, ContDiffAt ℝ 2 (fun y => christoffel g ginv y k i j) x)
    (ρ σ μ ν : Fin n) :
    DifferentiableAt ℝ (fun y => riemann g ginv y ρ σ μ ν) x := by
  have hΓD : ∀ k i j, DifferentiableAt ℝ (fun y => christoffel g ginv y k i j) x :=
    fun k i j => (hΓC2 k i j).differentiableAt two_ne_zero
  have hdΓD : ∀ a k i j,
      DifferentiableAt ℝ (fun y => CoordinateCurvature.coordDeriv a (fun z => christoffel g ginv z k
        i j) y) x :=
    fun a k i j => (contDiffAt_one_pd (hΓC2 k i j) a).differentiableAt one_ne_zero
  unfold riemann
  exact ((hdΓD μ ρ ν σ).sub (hdΓD ν ρ μ σ)).add
    (DifferentiableAt.fun_sum fun l _ =>
      ((hΓD ρ μ l).mul (hΓD l ν σ)).sub ((hΓD ρ ν l).mul (hΓD l μ σ)))

/-- Differentiability of `CoordinateCurvature.ricciTensor` from `C²` Christoffel symbols. -/
lemma differentiableAt_ricciOf {n : ℕ} (g ginv : (Fin n → ℝ) → Tensor2 n) {x : Fin n → ℝ}
    (hΓC2 : ∀ k i j, ContDiffAt ℝ 2 (fun y => christoffel g ginv y k i j) x)
    (σ ν : Fin n) :
    DifferentiableAt ℝ (fun y => CoordinateCurvature.ricciTensor g ginv y σ ν) x := by
  unfold CoordinateCurvature.ricciTensor
  exact DifferentiableAt.fun_sum fun ρ _ => differentiableAt_riemann g ginv hΓC2 ρ σ ρ ν

/-- Differentiability of `CoordinateCurvature.ricciScalar` from `C²` Christoffel symbols and
differentiable `ginv`. -/
lemma differentiableAt_scalarOf {n : ℕ} (g ginv : (Fin n → ℝ) → Tensor2 n) {x : Fin n → ℝ}
    (hginvD : ∀ i j, DifferentiableAt ℝ (fun y => ginv y i j) x)
    (hΓC2 : ∀ k i j, ContDiffAt ℝ 2 (fun y => christoffel g ginv y k i j) x) :
    DifferentiableAt ℝ (CoordinateCurvature.ricciScalar g ginv) x := by
  unfold CoordinateCurvature.ricciScalar
  exact DifferentiableAt.fun_sum fun σ _ =>
    DifferentiableAt.fun_sum fun ν _ =>
      (hginvD σ ν).mul (differentiableAt_ricciOf g ginv hΓC2 σ ν)

/-- Contracting `ρ = μ` in `covDerivRiemann` yields `covDeriv2` of the Ricci tensor. -/
lemma sum_covDerivRiemann_ricci {n : ℕ} (g ginv : (Fin n → ℝ) → Tensor2 n) {x : Fin n → ℝ}
    (hΓC2 : ∀ k i j, ContDiffAt ℝ 2 (fun y => christoffel g ginv y k i j) x)
    (m σ l : Fin n) :
    (∑ r, covDerivRiemann g ginv x m r σ r l) =
      covDeriv2 g ginv (CoordinateCurvature.ricciTensor g ginv) x m σ l := by
  simp only [covDerivRiemann, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have hpd : (∑ r, CoordinateCurvature.coordDeriv m (fun y => riemann g ginv y r σ r l) x) =
      CoordinateCurvature.coordDeriv m (fun y => CoordinateCurvature.ricciTensor g ginv y σ l) x :=
    (coordDeriv_sum m (fun r y => riemann g ginv y r σ r l) x
      (fun r => slice_differentiableAt m
        (differentiableAt_riemann g ginv hΓC2 r σ r l))).symm
  have hcancel :
      (∑ r, ∑ a, christoffel g ginv x r m a * riemann g ginv x a σ r l) =
      (∑ r, ∑ a, christoffel g ginv x a m r * riemann g ginv x r σ a l) := by
    rw [Finset.sum_comm]
  have hsig :
      (∑ r, ∑ a, christoffel g ginv x a m σ * riemann g ginv x r a r l) =
      (∑ a, christoffel g ginv x a m σ * CoordinateCurvature.ricciTensor g ginv x a l) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    rw [← Finset.mul_sum]
    rfl
  have hl :
      (∑ r, ∑ a, christoffel g ginv x a m l * riemann g ginv x r σ r a) =
      (∑ a, christoffel g ginv x a m l * CoordinateCurvature.ricciTensor g ginv x σ a) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    rw [← Finset.mul_sum]
    rfl
  unfold covDeriv2
  rw [hpd, hcancel, hsig, hl]
  ring

/-- The coordinate derivative of the inverse metric in terms of the metric
derivative: `∂_a g^{ij} = -Γ^i_{ac} g^{cj} - Γ^j_{ac} g^{ic}`. -/
lemma coordDeriv_ginv {n : ℕ} (g ginv : (Fin n → ℝ) → Tensor2 n) {x : Fin n → ℝ}
    (hgSymm : ∀ᶠ y in 𝓝 x, ∀ i j, g y i j = g y j i)
    (hInvL : ∀ᶠ y in 𝓝 x, ∀ i j, ∑ k, ginv y i k * g y k j = if i = j then 1 else 0)
    (hInvR : ∀ i j, ∑ k, g x i k * ginv x k j = if i = j then 1 else 0)
    (hginvSymm : ∀ i j, ginv x i j = ginv x j i)
    (hgD : ∀ i j, DifferentiableAt ℝ (fun y => g y i j) x)
    (hginvD : ∀ i j, DifferentiableAt ℝ (fun y => ginv y i j) x)
    (a i j : Fin n) :
    CoordinateCurvature.coordDeriv a (fun y => ginv y i j) x =
      -(∑ c, christoffel g ginv x i a c * ginv x c j)
        - ∑ c, christoffel g ginv x j a c * ginv x i c := by
  have h := inv_metric_compat g ginv hgSymm hInvL hInvR hginvSymm hgD hginvD a i j
  unfold covDeriv2Up at h
  linarith

/-- The three contracted second Bianchi terms, with the inverse metric folded in,
sum to zero. -/
lemma sum_covDerivRiemann_second_bianchi {n : ℕ} (g ginv : (Fin n → ℝ) → Tensor2 n) {x : Fin n → ℝ}
    (hgSymm : ∀ᶠ y in 𝓝 x, ∀ i j, g y i j = g y j i)
    (hΓC2 : ∀ k i j, ContDiffAt ℝ 2 (fun y => christoffel g ginv y k i j) x)
    (l : Fin n) :
    (∑ m, ∑ σ, ginv x m σ * ∑ r, covDerivRiemann g ginv x m r σ r l)
    + (∑ m, ∑ σ, ginv x m σ * ∑ r, covDerivRiemann g ginv x r r σ l m)
    + (∑ m, ∑ σ, ginv x m σ * ∑ r, covDerivRiemann g ginv x l r σ m r) = 0 := by
  have hpt : ∀ m σ r : Fin n,
      covDerivRiemann g ginv x m r σ r l
        + covDerivRiemann g ginv x r r σ l m
        + covDerivRiemann g ginv x l r σ m r = 0 :=
    fun m σ r => second_bianchi g ginv hgSymm hΓC2 m r σ r l
  calc
    (∑ m, ∑ σ, ginv x m σ * ∑ r, covDerivRiemann g ginv x m r σ r l)
      + (∑ m, ∑ σ, ginv x m σ * ∑ r, covDerivRiemann g ginv x r r σ l m)
      + (∑ m, ∑ σ, ginv x m σ * ∑ r, covDerivRiemann g ginv x l r σ m r)
        = ∑ m, ∑ σ, ginv x m σ * ∑ r,
            (covDerivRiemann g ginv x m r σ r l
              + covDerivRiemann g ginv x r r σ l m
              + covDerivRiemann g ginv x l r σ m r) := by
          simp_rw [← Finset.sum_add_distrib, ← mul_add, ← Finset.sum_add_distrib]
    _ = 0 := by
          apply Finset.sum_eq_zero
          intro m _
          apply Finset.sum_eq_zero
          intro σ _
          rw [Finset.sum_eq_zero (fun r _ => hpt m σ r), mul_zero]

/-- Contracting the first second-Bianchi term with the inverse metric gives the
covariant divergence of the Ricci tensor. -/
lemma sum_ginv_covDerivRiemann_ricci {n : ℕ} (g ginv : (Fin n → ℝ) → Tensor2 n) {x : Fin n → ℝ}
    (hΓC2 : ∀ k i j, ContDiffAt ℝ 2 (fun y => christoffel g ginv y k i j) x)
    (l : Fin n) :
    (∑ m, ∑ σ, ginv x m σ * ∑ r, covDerivRiemann g ginv x m r σ r l) =
    covDiv2 g ginv (CoordinateCurvature.ricciTensor g ginv) x l := by
  unfold covDiv2
  apply Finset.sum_congr rfl
  intro m _
  apply Finset.sum_congr rfl
  intro σ _
  rw [sum_covDerivRiemann_ricci g ginv hΓC2 m σ l]

/-- Contracting the third second-Bianchi term gives minus the coordinate derivative
of the Ricci scalar. -/
lemma sum_ginv_covDerivRiemann_scalar {n : ℕ} (g ginv : (Fin n → ℝ) → Tensor2 n) {x : Fin n → ℝ}
    (hginvSymm : ∀ᶠ y in 𝓝 x, ∀ i j, ginv y i j = ginv y j i)
    (hginvD : ∀ i j, DifferentiableAt ℝ (fun y => ginv y i j) x)
    (hΓC2 : ∀ k i j, ContDiffAt ℝ 2 (fun y => christoffel g ginv y k i j) x)
    (hInvUp : ∀ a i j, CoordinateCurvature.coordDeriv a (fun y => ginv y i j) x =
      -(∑ c, christoffel g ginv x i a c * ginv x c j)
        - ∑ c, christoffel g ginv x j a c * ginv x i c)
    (l : Fin n) :
    (∑ m, ∑ σ, ginv x m σ * ∑ r, covDerivRiemann g ginv x l r σ m r) =
    -CoordinateCurvature.coordDeriv l (CoordinateCurvature.ricciScalar g ginv) x := by
  have hRicD : ∀ σ ν,
      DifferentiableAt ℝ (fun y => CoordinateCurvature.ricciTensor g ginv y σ ν) x :=
    fun σ ν => differentiableAt_ricciOf g ginv hΓC2 σ ν
  have hpdS : CoordinateCurvature.coordDeriv l (CoordinateCurvature.ricciScalar g ginv) x =
      ∑ m, ∑ σ, (CoordinateCurvature.coordDeriv l (fun y => ginv y m σ) x
        * CoordinateCurvature.ricciTensor g ginv x m σ
        + ginv x m σ
          * CoordinateCurvature.coordDeriv l (fun y => CoordinateCurvature.ricciTensor g ginv y m σ)
          x) := by
    unfold CoordinateCurvature.ricciScalar
    rw [coordDeriv_sum l
      (fun m y => ∑ σ, ginv y m σ * CoordinateCurvature.ricciTensor g ginv y m σ) x
      (fun m => slice_differentiableAt l
        (DifferentiableAt.fun_sum fun σ _ => (hginvD m σ).fun_mul (hRicD m σ)))]
    apply Finset.sum_congr rfl
    intro m _
    rw [coordDeriv_sum l
      (fun σ y => ginv y m σ * CoordinateCurvature.ricciTensor g ginv y m σ) x
      (fun σ => slice_differentiableAt l ((hginvD m σ).fun_mul (hRicD m σ)))]
    apply Finset.sum_congr rfl
    intro σ _
    exact coordDeriv_mul l x (slice_differentiableAt l (hginvD m σ))
      (slice_differentiableAt l (hRicD m σ))
  have hric_neg : ∀ m σ,
      (∑ r, covDerivRiemann g ginv x l r σ m r) =
        -covDeriv2 g ginv (CoordinateCurvature.ricciTensor g ginv) x l σ m := by
    intro m σ
    have hskew_cov : ∀ r, covDerivRiemann g ginv x l r σ m r =
        -covDerivRiemann g ginv x l r σ r m := by
      intro r
      have hpd_skew : CoordinateCurvature.coordDeriv l (fun y => riemann g ginv y r σ m r) x =
          -CoordinateCurvature.coordDeriv l (fun y => riemann g ginv y r σ r m) x := by
        rw [coordDeriv_congr l x (fun y => riemann_skew_last g ginv y r σ m r),
          coordDeriv_neg]
      unfold covDerivRiemann
      rw [hpd_skew]
      have h1 : ∀ a, riemann g ginv x a σ m r = -riemann g ginv x a σ r m :=
        fun a => riemann_skew_last g ginv x a σ m r
      have h2 : ∀ a, riemann g ginv x r a m r = -riemann g ginv x r a r m :=
        fun a => riemann_skew_last g ginv x r a m r
      have h3 : ∀ a, riemann g ginv x r σ a r = -riemann g ginv x r σ r a :=
        fun a => riemann_skew_last g ginv x r σ a r
      have h4 : ∀ a, riemann g ginv x r σ m a = -riemann g ginv x r σ a m :=
        fun a => riemann_skew_last g ginv x r σ m a
      simp_rw [h1, h2, h3, h4, mul_neg, Finset.sum_neg_distrib]
      ring
    simp_rw [hskew_cov, Finset.sum_neg_distrib, sum_covDerivRiemann_ricci g ginv hΓC2 l σ m]
  simp_rw [hric_neg, mul_neg, Finset.sum_neg_distrib]
  rw [hpdS]
  congr 1
  have hginv0 : ∀ a b, ginv x a b = ginv x b a := hginvSymm.self_of_nhds
  have hmain :
      (∑ m, ∑ σ, ginv x m σ * covDeriv2 g ginv (CoordinateCurvature.ricciTensor g ginv) x l σ m) =
      (∑ m, ∑ σ, (CoordinateCurvature.coordDeriv l (fun y => ginv y m σ) x
        * CoordinateCurvature.ricciTensor g ginv x σ m
        + ginv x m σ
          * CoordinateCurvature.coordDeriv l (fun y => CoordinateCurvature.ricciTensor g ginv y σ m)
          x)) := by
    simp only [covDeriv2, mul_sub, Finset.sum_sub_distrib, hInvUp]
    have hA :
        (∑ m, ∑ σ, ginv x m σ * ∑ a, christoffel g ginv x a l σ
          * CoordinateCurvature.ricciTensor g ginv x a m) =
        (∑ m, ∑ σ, (∑ c, christoffel g ginv x σ l c * ginv x m c)
          * CoordinateCurvature.ricciTensor g ginv x σ m) := by
      apply Finset.sum_congr rfl
      intro m _
      simp_rw [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro σ _
      apply Finset.sum_congr rfl
      intro c _
      ring
    have hB :
        (∑ m, ∑ σ, ginv x m σ * ∑ a, christoffel g ginv x a l m
          * CoordinateCurvature.ricciTensor g ginv x σ a) =
        (∑ m, ∑ σ, (∑ c, christoffel g ginv x m l c * ginv x c σ)
          * CoordinateCurvature.ricciTensor g ginv x σ m) := by
      rw [Finset.sum_comm]
      conv_rhs => rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro σ _
      simp_rw [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro m _
      apply Finset.sum_congr rfl
      intro c _
      rw [hginv0 c σ]
      ring
    have hsplit :
        (∑ m, ∑ σ, ((-(∑ c, christoffel g ginv x m l c * ginv x c σ)
          - ∑ c, christoffel g ginv x σ l c * ginv x m c)
            * CoordinateCurvature.ricciTensor g ginv x σ m
          + ginv x m σ
            * CoordinateCurvature.coordDeriv l (fun y => CoordinateCurvature.ricciTensor g ginv y σ
            m) x)) =
        (∑ m, ∑ σ, ginv x m σ
          * CoordinateCurvature.coordDeriv l (fun y => CoordinateCurvature.ricciTensor g ginv y σ m)
          x)
          - (∑ m, ∑ σ, (∑ c, christoffel g ginv x σ l c * ginv x m c)
            * CoordinateCurvature.ricciTensor g ginv x σ m)
          - (∑ m, ∑ σ, (∑ c, christoffel g ginv x m l c * ginv x c σ)
            * CoordinateCurvature.ricciTensor g ginv x σ m) := by
      simp_rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro m _
      apply Finset.sum_congr rfl
      intro σ _
      ring
    rw [hsplit, ← hA, ← hB]
  rw [hmain]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m _
  apply Finset.sum_congr rfl
  intro σ _
  have hpd_g_sym : CoordinateCurvature.coordDeriv l (fun y => ginv y σ m) x =
      CoordinateCurvature.coordDeriv l (fun y => ginv y m σ) x :=
    coordDeriv_congr_nhds l x (hginvSymm.mono fun y hy => hy σ m)
  rw [hpd_g_sym, hginv0 σ m]

/-- A double contraction of the Riemann tensor with the inverse metric is the Ricci
contraction with one inverse metric, near `x`. -/
lemma sum_ginv_riemann_ricci {n : ℕ} (g ginv : (Fin n → ℝ) → Tensor2 n) {x : Fin n → ℝ}
    (hgSymm : ∀ᶠ y in 𝓝 x, ∀ i j, g y i j = g y j i)
    (hginvSymm : ∀ᶠ y in 𝓝 x, ∀ i j, ginv y i j = ginv y j i)
    (hInvL : ∀ᶠ y in 𝓝 x, ∀ i j, ∑ k, ginv y i k * g y k j = if i = j then 1 else 0)
    (hInvR : ∀ᶠ y in 𝓝 x, ∀ i j, ∑ k, g y i k * ginv y k j = if i = j then 1 else 0)
    (hgC2 : ∀ i j, ContDiffAt ℝ 2 (fun y => g y i j) x)
    (hΓC2 : ∀ k i j, ContDiffAt ℝ 2 (fun y => christoffel g ginv y k i j) x) :
    ∀ r a : Fin n,
    (fun y => ∑ m, ∑ σ, ginv y m σ * riemann g ginv y r σ a m) =ᶠ[𝓝 x]
    fun y => ∑ m, ginv y r m * CoordinateCurvature.ricciTensor g ginv y m a := by
  intro r a
  have hS : ∀ᶠ y in 𝓝 x, ∀ᶠ z in 𝓝 y, ∀ i j, g z i j = g z j i :=
    eventually_eventually_nhds.mpr hgSymm
  have hI : ∀ᶠ y in 𝓝 x, ∀ᶠ z in 𝓝 y, ∀ m j,
      ∑ k, ginv z k m * g z k j = if m = j then 1 else 0 := by
    have h0 : ∀ᶠ y in 𝓝 x, ∀ m j, ∑ k, ginv y k m * g y k j = if m = j then 1 else 0 := by
      filter_upwards [hginvSymm, hInvL] with y hyS hyL m j
      simpa [hyS] using hyL m j
    exact eventually_eventually_nhds.mpr h0
  have hC2_ev : ∀ᶠ y in 𝓝 x, ∀ i j, ContDiffAt ℝ 2 (fun z => g z i j) y := by
    have hall : ∀ i j : Fin n, ∀ᶠ y in 𝓝 x, ContDiffAt ℝ 2 (fun z => g z i j) y := by
      intro i j
      obtain ⟨u, hu, h'u⟩ := (hgC2 i j).contDiffOn (m := 2) le_rfl (by simp)
      rcases mem_nhds_iff.1 hu with ⟨v, vu, v_open, xv⟩
      filter_upwards [v_open.mem_nhds xv] with y hy
      exact (h'u.mono vu y hy).contDiffAt (v_open.mem_nhds hy)
    exact eventually_all.mpr fun i => eventually_all.mpr fun j => hall i j
  have hΓD_ev : ∀ᶠ y in 𝓝 x, ∀ k i j,
      DifferentiableAt ℝ (fun z => christoffel g ginv z k i j) y :=
    eventually_all.mpr fun k => eventually_all.mpr fun i => eventually_all.mpr fun j =>
      eventually_differentiableAt_of_contDiffAt_two (hΓC2 k i j)
  filter_upwards [hS, hI, hInvL, hInvR, hginvSymm, hC2_ev, hΓD_ev] with
    y hyS hyI hyL _hyR _hyGS hyC2 hyΓD
  have hskew1 : ∀ α σ m,
      (∑ β, g y α β * riemann g ginv y β σ a m) =
      -(∑ β, g y σ β * riemann g ginv y β α a m) := by
    intro α σ m
    have h := riemann_lower_skew_first g ginv hyS hyI hyC2 hyΓD α σ a m
    linarith
  calc
    ∑ m, ∑ σ, ginv y m σ * riemann g ginv y r σ a m
        = ∑ m, ∑ σ, ginv y m σ *
            ∑ β, (if r = β then 1 else 0) * riemann g ginv y β σ a m := by
          simp
    _ = ∑ m, ∑ σ, ginv y m σ *
            ∑ α, ginv y r α * (∑ β, g y α β * riemann g ginv y β σ a m) := by
          apply Finset.sum_congr rfl
          intro m _
          apply Finset.sum_congr rfl
          intro σ _
          congr 1
          simp_rw [Finset.mul_sum]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro β _
          have hfac : (∑ α, ginv y r α * (g y α β * riemann g ginv y β σ a m)) =
              (∑ α, ginv y r α * g y α β) * riemann g ginv y β σ a m := by
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro α _
            ring
          rw [hfac, hyL r β]
    _ = ∑ m, ∑ σ, ginv y m σ *
            ∑ α, ginv y r α * (-(∑ β, g y σ β * riemann g ginv y β α a m)) := by
          apply Finset.sum_congr rfl
          intro m _
          apply Finset.sum_congr rfl
          intro σ _
          congr 1
          apply Finset.sum_congr rfl
          intro α _
          rw [hskew1 α σ m]
    _ = ∑ α, ginv y r α * ∑ m, (-riemann g ginv y m α a m) := by
          have h1 :
              (∑ m, ∑ σ, ginv y m σ *
                ∑ α, ginv y r α * (-(∑ β, g y σ β * riemann g ginv y β α a m))) =
              ∑ α, ginv y r α * ∑ m, ∑ β,
                -(∑ σ, ginv y m σ * g y σ β) * riemann g ginv y β α a m := by
            have hexp : ∀ m σ α,
                ginv y m σ * (ginv y r α * (-(∑ β, g y σ β * riemann g ginv y β α a m))) =
                ∑ β, -(ginv y r α * (ginv y m σ * g y σ β * riemann g ginv y β α a m)) := by
              intro m σ α
              rw [mul_neg, mul_neg, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]
              apply Finset.sum_congr rfl
              intro β _
              ring
            conv_lhs =>
              arg 2; ext m; arg 2; ext σ
              rw [Finset.mul_sum]
            simp_rw [hexp]
            rw [Finset.sum_comm]
            conv_lhs => arg 2; ext σ; rw [Finset.sum_comm]
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro α _
            rw [Finset.sum_comm]
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro m _
            rw [Finset.sum_comm, Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro β _
            rw [neg_mul, Finset.sum_mul, ← Finset.sum_neg_distrib, Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro σ _
            ring
          rw [h1]
          apply Finset.sum_congr rfl
          intro α _
          congr 1
          apply Finset.sum_congr rfl
          intro m _
          simp_rw [hyL m]
          simp
    _ = ∑ m, ginv y r m * CoordinateCurvature.ricciTensor g ginv y m a := by
          apply Finset.sum_congr rfl
          intro α _
          congr 1
          unfold CoordinateCurvature.ricciTensor
          apply Finset.sum_congr rfl
          intro m _
          rw [riemann_skew_last g ginv y m α a m]
          ring

/-- Contracting the second second-Bianchi term with the inverse metric gives the
covariant divergence of the Ricci tensor. -/
lemma sum_ginv_covDerivRiemann_ricci_div {n : ℕ} (g ginv : (Fin n → ℝ) → Tensor2 n) {x : Fin n → ℝ}
    (hginvSymm : ∀ᶠ y in 𝓝 x, ∀ i j, ginv y i j = ginv y j i)
    (hginvD : ∀ i j, DifferentiableAt ℝ (fun y => ginv y i j) x)
    (hΓC2 : ∀ k i j, ContDiffAt ℝ 2 (fun y => christoffel g ginv y k i j) x)
    (hRcontract_nhds : ∀ r a : Fin n,
      (fun y => ∑ m, ∑ σ, ginv y m σ * riemann g ginv y r σ a m) =ᶠ[𝓝 x]
        fun y => ∑ m, ginv y r m * CoordinateCurvature.ricciTensor g ginv y m a)
    (hInvUp : ∀ a i j, CoordinateCurvature.coordDeriv a (fun y => ginv y i j) x =
      -(∑ c, christoffel g ginv x i a c * ginv x c j)
        - ∑ c, christoffel g ginv x j a c * ginv x i c)
    (l : Fin n) :
    (∑ m, ∑ σ, ginv x m σ * ∑ r, covDerivRiemann g ginv x r r σ l m) =
    covDiv2 g ginv (CoordinateCurvature.ricciTensor g ginv) x l := by
  have hRD : ∀ ρ σ μ ν, DifferentiableAt ℝ (fun y => riemann g ginv y ρ σ μ ν) x :=
    fun ρ σ μ ν => differentiableAt_riemann g ginv hΓC2 ρ σ μ ν
  have hRicD : ∀ σ ν,
      DifferentiableAt ℝ (fun y => CoordinateCurvature.ricciTensor g ginv y σ ν) x :=
    fun σ ν => differentiableAt_ricciOf g ginv hΓC2 σ ν
  have hginv0 : ∀ a b, ginv x a b = ginv x b a := hginvSymm.self_of_nhds
  have hstep : ∀ r,
      (∑ m, ∑ σ, ginv x m σ * covDerivRiemann g ginv x r r σ l m) =
        CoordinateCurvature.coordDeriv r
          (fun y => ∑ m, ∑ σ, ginv y m σ * riemann g ginv y r σ l m) x
        + ∑ a, christoffel g ginv x r r a *
            (∑ m, ∑ σ, ginv x m σ * riemann g ginv x a σ l m)
        - ∑ a, christoffel g ginv x a r l *
            (∑ m, ∑ σ, ginv x m σ * riemann g ginv x r σ a m) := by
    intro r
    have hpd_lhs :
        CoordinateCurvature.coordDeriv r (fun y => ∑ m, ∑ σ, ginv y m σ
          * riemann g ginv y r σ l m) x =
          ∑ m, ∑ σ, (CoordinateCurvature.coordDeriv r (fun y => ginv y m σ) x
            * riemann g ginv x r σ l m
            + ginv x m σ
              * CoordinateCurvature.coordDeriv r (fun y => riemann g ginv y r σ l m) x) := by
      rw [coordDeriv_sum r
        (fun m y => ∑ σ, ginv y m σ * riemann g ginv y r σ l m) x
        (fun m => slice_differentiableAt r
          (DifferentiableAt.fun_sum fun σ _ => (hginvD m σ).fun_mul (hRD r σ l m)))]
      apply Finset.sum_congr rfl
      intro m _
      rw [coordDeriv_sum r
        (fun σ y => ginv y m σ * riemann g ginv y r σ l m) x
        (fun σ => slice_differentiableAt r ((hginvD m σ).fun_mul (hRD r σ l m)))]
      apply Finset.sum_congr rfl
      intro σ _
      exact coordDeriv_mul r x (slice_differentiableAt r (hginvD m σ))
        (slice_differentiableAt r (hRD r σ l m))
    have hsplit :
        (∑ m, ∑ σ, ((CoordinateCurvature.coordDeriv r (fun y => ginv y m σ) x)
          * riemann g ginv x r σ l m
          + ginv x m σ * CoordinateCurvature.coordDeriv r (fun y => riemann g ginv y r σ l m) x)) =
        (∑ m, ∑ σ, ginv x m σ
          * CoordinateCurvature.coordDeriv r (fun y => riemann g ginv y r σ l m) x)
          - (∑ m, ∑ σ, (∑ c, christoffel g ginv x σ r c * ginv x m c) *
              riemann g ginv x r σ l m)
          - (∑ m, ∑ σ, (∑ c, christoffel g ginv x m r c * ginv x c σ) *
              riemann g ginv x r σ l m) := by
      simp_rw [hInvUp]
      have heach : ∀ m σ,
          (-(∑ c, christoffel g ginv x m r c * ginv x c σ)
            - ∑ c, christoffel g ginv x σ r c * ginv x m c) * riemann g ginv x r σ l m
            + ginv x m σ * CoordinateCurvature.coordDeriv r (fun y => riemann g ginv y r σ l m) x =
          ginv x m σ * CoordinateCurvature.coordDeriv r (fun y => riemann g ginv y r σ l m) x
            - (∑ c, christoffel g ginv x σ r c * ginv x m c) * riemann g ginv x r σ l m
            - (∑ c, christoffel g ginv x m r c * ginv x c σ) * riemann g ginv x r σ l m := by
        intro m σ; ring
      have hstep_sum :
          (∑ m, ∑ σ,
            ((-(∑ c, christoffel g ginv x m r c * ginv x c σ)
              - ∑ c, christoffel g ginv x σ r c * ginv x m c) * riemann g ginv x r σ l m
              + ginv x m σ
                * CoordinateCurvature.coordDeriv r (fun y => riemann g ginv y r σ l m) x)) =
          ∑ m, ∑ σ,
            (ginv x m σ * CoordinateCurvature.coordDeriv r (fun y => riemann g ginv y r σ l m) x
              - (∑ c, christoffel g ginv x σ r c * ginv x m c) * riemann g ginv x r σ l m
              - (∑ c, christoffel g ginv x m r c * ginv x c σ) * riemann g ginv x r σ l m) := by
        apply Finset.sum_congr rfl
        intro m _
        apply Finset.sum_congr rfl
        intro σ _
        exact heach m σ
      rw [hstep_sum]
      simp_rw [Finset.sum_sub_distrib]
    rw [hpd_lhs, hsplit]
    simp only [covDerivRiemann, mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    have hA :
        (∑ m, ∑ σ, ginv x m σ * ∑ a, christoffel g ginv x r r a * riemann g ginv x a σ l m) =
        (∑ a, christoffel g ginv x r r a * ∑ m, ∑ σ, ginv x m σ * riemann g ginv x a σ l m) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      conv_lhs => arg 2; ext σ; rw [Finset.sum_comm]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro m _
      apply Finset.sum_congr rfl
      intro σ _
      ring
    have hB :
        (∑ m, ∑ σ, ginv x m σ * ∑ a, christoffel g ginv x a r l * riemann g ginv x r σ a m) =
        (∑ a, christoffel g ginv x a r l * ∑ m, ∑ σ, ginv x m σ * riemann g ginv x r σ a m) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      conv_lhs => arg 2; ext σ; rw [Finset.sum_comm]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro m _
      apply Finset.sum_congr rfl
      intro σ _
      ring
    have hC :
        (∑ m, ∑ σ, ginv x m σ * ∑ a, christoffel g ginv x a r σ * riemann g ginv x r a l m) =
        (∑ m, ∑ σ, (∑ c, christoffel g ginv x σ r c * ginv x m c) *
          riemann g ginv x r σ l m) := by
      apply Finset.sum_congr rfl
      intro m _
      simp_rw [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro σ _
      apply Finset.sum_congr rfl
      intro c _
      rw [hginv0 m c]
      ring
    have hD :
        (∑ m, ∑ σ, ginv x m σ * ∑ a, christoffel g ginv x a r m * riemann g ginv x r σ l a) =
        (∑ m, ∑ σ, (∑ c, christoffel g ginv x m r c * ginv x c σ) *
          riemann g ginv x r σ l m) := by
      rw [Finset.sum_comm]
      conv_rhs => rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro σ _
      simp_rw [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro m _
      apply Finset.sum_congr rfl
      intro c _
      rw [hginv0 c σ]
      ring
    rw [hA, hB, hC, hD]
    ring
  have hreord :
      (∑ m, ∑ σ, ginv x m σ * ∑ r, covDerivRiemann g ginv x r r σ l m) =
      ∑ r, ∑ m, ∑ σ, ginv x m σ * covDerivRiemann g ginv x r r σ l m := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    conv_lhs => arg 2; ext σ; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro r _
    rw [Finset.sum_comm]
  rw [hreord]
  simp_rw [hstep]
  have hstep2 : ∀ r,
      CoordinateCurvature.coordDeriv r (fun y => ∑ m, ∑ σ, ginv y m σ * riemann g ginv y r σ l m) x
        + (∑ a, christoffel g ginv x r r a *
            ∑ m, ∑ σ, ginv x m σ * riemann g ginv x a σ l m)
        - (∑ a, christoffel g ginv x a r l *
            ∑ m, ∑ σ, ginv x m σ * riemann g ginv x r σ a m) =
      ∑ m, ginv x r m * covDeriv2 g ginv (CoordinateCurvature.ricciTensor g ginv) x r m l := by
    intro r
    rw [coordDeriv_congr_nhds r x (hRcontract_nhds r l)]
    simp_rw [(hRcontract_nhds _ l).self_of_nhds, (hRcontract_nhds r _).self_of_nhds]
    rw [coordDeriv_sum r
      (fun m y => ginv y r m * CoordinateCurvature.ricciTensor g ginv y m l) x
      (fun m => slice_differentiableAt r ((hginvD r m).fun_mul (hRicD m l)))]
    have hpm : ∀ m, CoordinateCurvature.coordDeriv r (fun y => ginv y r m
      * CoordinateCurvature.ricciTensor g ginv y m l) x =
        CoordinateCurvature.coordDeriv r (fun y => ginv y r m) x
          * CoordinateCurvature.ricciTensor g ginv x m l
          + ginv x r m
            * CoordinateCurvature.coordDeriv r (fun y => CoordinateCurvature.ricciTensor g ginv y m
            l) x :=
      fun m => coordDeriv_mul r x (slice_differentiableAt r (hginvD r m))
        (slice_differentiableAt r (hRicD m l))
    simp_rw [hpm, hInvUp]
    simp only [covDeriv2, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    have hX :
        (∑ a, christoffel g ginv x r r a * ∑ m, ginv x a m
          * CoordinateCurvature.ricciTensor g ginv x m l) =
        (∑ m, (∑ c, christoffel g ginv x r r c * ginv x c m)
          * CoordinateCurvature.ricciTensor g ginv x m l) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro m _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro c _
      ring
    have hY :
        (∑ m, ginv x r m * ∑ a, christoffel g ginv x a r m
          * CoordinateCurvature.ricciTensor g ginv x a l) =
        (∑ m, (∑ c, christoffel g ginv x m r c * ginv x r c)
          * CoordinateCurvature.ricciTensor g ginv x m l) := by
      simp_rw [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro m _
      apply Finset.sum_congr rfl
      intro c _
      ring
    have hZ :
        (∑ a, christoffel g ginv x a r l * ∑ m, ginv x r m
          * CoordinateCurvature.ricciTensor g ginv x m a) =
        (∑ m, ginv x r m * ∑ a, christoffel g ginv x a r l
          * CoordinateCurvature.ricciTensor g ginv x m a) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro m _
      apply Finset.sum_congr rfl
      intro a _
      ring
    have hsplit :
        (∑ m, (-(∑ c, christoffel g ginv x r r c * ginv x c m)
          - ∑ c, christoffel g ginv x m r c * ginv x r c)
            * CoordinateCurvature.ricciTensor g ginv x m l) =
        -(∑ m, (∑ c, christoffel g ginv x r r c * ginv x c m)
          * CoordinateCurvature.ricciTensor g ginv x m l)
          - (∑ m, (∑ c, christoffel g ginv x m r c * ginv x r c)
            * CoordinateCurvature.ricciTensor g ginv x m l) := by
      have hm : ∀ m,
          (-(∑ c, christoffel g ginv x r r c * ginv x c m)
            - ∑ c, christoffel g ginv x m r c * ginv x r c)
              * CoordinateCurvature.ricciTensor g ginv x m l =
          -((∑ c, christoffel g ginv x r r c * ginv x c m)
            * CoordinateCurvature.ricciTensor g ginv x m l)
            - (∑ c, christoffel g ginv x m r c * ginv x r c)
              * CoordinateCurvature.ricciTensor g ginv x m l := by
        intro m; ring
      simp_rw [hm, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
    rw [hsplit, hX, hY, hZ]
    ring
  simp_rw [hstep2]
  rfl

/-- **General Contracted Bianchi Identity**:
`∇^μ Ric_{μl} = (1/2) ∂_l S` in arbitrary dimension `n`. -/
lemma contracted_bianchi {n : ℕ} (g ginv : (Fin n → ℝ) → Tensor2 n) {x : Fin n → ℝ}
    (hgSymm : ∀ᶠ y in 𝓝 x, ∀ i j, g y i j = g y j i)
    (hginvSymm : ∀ᶠ y in 𝓝 x, ∀ i j, ginv y i j = ginv y j i)
    (hInvL : ∀ᶠ y in 𝓝 x, ∀ i j, ∑ k, ginv y i k * g y k j = if i = j then 1 else 0)
    (hInvR : ∀ᶠ y in 𝓝 x, ∀ i j, ∑ k, g y i k * ginv y k j = if i = j then 1 else 0)
    (hgC2 : ∀ i j, ContDiffAt ℝ 2 (fun y => g y i j) x)
    (hginvD : ∀ i j, DifferentiableAt ℝ (fun y => ginv y i j) x)
    (hΓC2 : ∀ k i j, ContDiffAt ℝ 2 (fun y => christoffel g ginv y k i j) x)
    (l : Fin n) :
    covDiv2 g ginv (CoordinateCurvature.ricciTensor g ginv) x l = (1 / 2)
      * CoordinateCurvature.coordDeriv l (CoordinateCurvature.ricciScalar g ginv) x := by
  have hgD : ∀ i j, DifferentiableAt ℝ (fun y => g y i j) x :=
    fun i j => (hgC2 i j).differentiableAt two_ne_zero
  have hInvUp : ∀ a i j, CoordinateCurvature.coordDeriv a (fun y => ginv y i j) x =
      -(∑ c, christoffel g ginv x i a c * ginv x c j)
        - ∑ c, christoffel g ginv x j a c * ginv x i c :=
    fun a i j => coordDeriv_ginv g ginv hgSymm hInvL (hInvR.self_of_nhds)
      (hginvSymm.self_of_nhds) hgD hginvD a i j
  have hBsum := sum_covDerivRiemann_second_bianchi g ginv hgSymm hΓC2 l
  have hT1 := sum_ginv_covDerivRiemann_ricci g ginv hΓC2 l
  have hT3 := sum_ginv_covDerivRiemann_scalar g ginv hginvSymm hginvD hΓC2 hInvUp l
  have hT2 := sum_ginv_covDerivRiemann_ricci_div g ginv hginvSymm hginvD hΓC2
    (sum_ginv_riemann_ricci g ginv hgSymm hginvSymm hInvL hInvR hgC2 hΓC2) hInvUp l
  rw [hT1, hT2, hT3] at hBsum
  linarith
/-- **General Einstein tensor conservation**: `∇^μ G_{μl} = 0` in arbitrary
dimension `n`, proved from the contracted Bianchi identity and metric
compatibility. -/
lemma covDiv_einstein_eq_zero {n : ℕ} (g ginv : (Fin n → ℝ) → Tensor2 n) {x : Fin n → ℝ}
    (hgSymm : ∀ᶠ y in 𝓝 x, ∀ i j, g y i j = g y j i)
    (hginvSymm : ∀ᶠ y in 𝓝 x, ∀ i j, ginv y i j = ginv y j i)
    (hInvL : ∀ᶠ y in 𝓝 x, ∀ i j, ∑ k, ginv y i k * g y k j = if i = j then 1 else 0)
    (hInvR : ∀ᶠ y in 𝓝 x, ∀ i j, ∑ k, g y i k * ginv y k j = if i = j then 1 else 0)
    (hgC2 : ∀ i j, ContDiffAt ℝ 2 (fun y => g y i j) x)
    (hginvD : ∀ i j, DifferentiableAt ℝ (fun y => ginv y i j) x)
    (hΓC2 : ∀ k i j, ContDiffAt ℝ 2 (fun y => christoffel g ginv y k i j) x)
    (l : Fin n) :
    covDiv2 g ginv (CoordinateCurvature.einsteinTensor g ginv) x l = 0 := by
  have hgD : ∀ i j, DifferentiableAt ℝ (fun y => g y i j) x :=
    fun i j => (hgC2 i j).differentiableAt two_ne_zero
  have hRicD : ∀ σ ν,
      DifferentiableAt ℝ (fun y => CoordinateCurvature.ricciTensor g ginv y σ ν) x :=
    fun σ ν => differentiableAt_ricciOf g ginv hΓC2 σ ν
  have hSD : DifferentiableAt ℝ (CoordinateCurvature.ricciScalar g ginv) x :=
    differentiableAt_scalarOf g ginv hginvD hΓC2
  have hInvAt : ∀ m j, ∑ a, ginv x a m * g x a j = if m = j then 1 else 0 := by
    intro m j
    simpa [hginvSymm.self_of_nhds] using hInvL.self_of_nhds m j
  have hcd : ∀ μ ν,
      covDeriv2 g ginv (CoordinateCurvature.einsteinTensor g ginv) x μ ν l =
        covDeriv2 g ginv (CoordinateCurvature.ricciTensor g ginv) x μ ν l
          - (1 / 2) * CoordinateCurvature.coordDeriv μ (CoordinateCurvature.ricciScalar g ginv) x
            * g x ν l := by
    intro μ ν
    unfold covDeriv2 CoordinateCurvature.einsteinTensor
    have hsub := coordDeriv_sub μ x (slice_differentiableAt μ (hRicD ν l))
      (slice_differentiableAt μ ((hSD.const_mul (1 / 2 : ℝ)).fun_mul (hgD ν l)))
    have hmul := coordDeriv_mul μ x
      (slice_differentiableAt μ (hSD.const_mul (1 / 2 : ℝ)))
      (slice_differentiableAt μ (hgD ν l))
    have hcmul : CoordinateCurvature.coordDeriv μ
        (fun y => (1 / 2 : ℝ) * CoordinateCurvature.ricciScalar g ginv y) x
        = (1 / 2) * CoordinateCurvature.coordDeriv μ
            (CoordinateCurvature.ricciScalar g ginv) x :=
      coordDeriv_const_mul μ (1 / 2 : ℝ) x
    have hmc := metric_compat g ginv hgSymm hInvAt μ ν l
    unfold covDeriv2 at hmc
    rw [hsub, hmul, hcmul]
    simp_rw [mul_sub, Finset.sum_sub_distrib]
    have h1 :
        (∑ a, christoffel g ginv x a μ ν * ((1 / 2) * CoordinateCurvature.ricciScalar g ginv x
          * g x a l)) =
        (1 / 2) * CoordinateCurvature.ricciScalar g ginv x * ∑ a, christoffel g ginv x a μ ν
          * g x a l := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      ring
    have h2 :
        (∑ a, christoffel g ginv x a μ l * ((1 / 2) * CoordinateCurvature.ricciScalar g ginv x
          * g x ν a)) =
        (1 / 2) * CoordinateCurvature.ricciScalar g ginv x * ∑ a, christoffel g ginv x a μ l
          * g x ν a := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      ring
    rw [h1, h2]
    linear_combination -((1 / 2) * CoordinateCurvature.ricciScalar g ginv x) * hmc
  have hdiv :
      covDiv2 g ginv (CoordinateCurvature.einsteinTensor g ginv) x l =
        covDiv2 g ginv (CoordinateCurvature.ricciTensor g ginv) x l
          - (1 / 2)
            * CoordinateCurvature.coordDeriv l (CoordinateCurvature.ricciScalar g ginv) x := by
    unfold covDiv2
    simp_rw [hcd, mul_sub, Finset.sum_sub_distrib]
    congr 1
    calc
      ∑ μ, ∑ ν, ginv x μ ν * ((1 / 2)
        * CoordinateCurvature.coordDeriv μ (CoordinateCurvature.ricciScalar g ginv) x * g x ν l)
          = ∑ μ, (1 / 2)
            * CoordinateCurvature.coordDeriv μ (CoordinateCurvature.ricciScalar g ginv) x
            * (∑ ν, ginv x μ ν * g x ν l) := by
            apply Finset.sum_congr rfl
            intro μ _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro ν _
            ring
      _ = (1 / 2) * CoordinateCurvature.coordDeriv l
            (CoordinateCurvature.ricciScalar g ginv) x := by
            simp_rw [hInvL.self_of_nhds]
            simp
  rw [hdiv, contracted_bianchi g ginv hgSymm hginvSymm hInvL hInvR hgC2 hginvD hΓC2 l]
  ring

end Bianchi
end GeneralRelativity
