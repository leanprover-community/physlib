/-
Copyright (c) 2026 Alex Vergara Gil.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/

module

public import PhyslibAlpha.Relativity.General.ManifoldInterface
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Covariant derivatives, the Bianchi identities, and Einstein conservation

## i. Overview

This module proves the general differential curvature identities in arbitrary
dimension `n : ℕ` for any smooth coordinate metric `(g, ginv)`.  The general
contracted Bianchi identity and Einstein tensor conservation are in
`General/BianchiContracted.lean`, and their chart-level case is in
`General/BianchiChart.lean`.

## ii. Key results

* Schwarz symmetry of coordinate partial derivatives
  `CoordinateCurvature.coordDeriv_comm`
  from Mathlib's `ContDiffAt.isSymmSndFDerivAt`;
* general metric compatibility `metric_compat` (`∇_λ g_{ij} = 0`) and inverse
  metric compatibility `inv_metric_compat` (`∇_λ g^{ij} = 0`);
* skew-symmetry of the lowered Riemann tensor in its first pair
  `riemann_lower_skew_first` (`R_{ασμν} + R_{σαμν} = 0`);
* the algebraic first Bianchi identity `riemann_bianchi`
  (`R^ρ_{σμν} + R^ρ_{μνσ} + R^ρ_{νσμ} = 0`);
* the lowered first Bianchi identity `riemann_lower_bianchi` and pair symmetry
  `riemann_lower_pair_symm` (`R_{ασμν} = R_{μνασ}`);
* the general second Bianchi identity `second_bianchi` in arbitrary coordinates
  (without assuming normal coordinates);
* the contraction lemmas `coordDeriv_ginv`, `sum_covDerivRiemann_second_bianchi`
  and the three `sum_ginv_covDerivRiemann_*` contractions, which
  `General/BianchiContracted.lean` uses to prove the contracted Bianchi
  identity.

## iii. Table of contents

- A. Partial-derivative calculus and Schwarz symmetry
- B. Covariant derivatives and divergence
- C. Metric compatibility and Riemann symmetries
- D. General Second Bianchi Identity

## iv. References

* S. M. Carroll, *Lecture Notes on General Relativity*, arXiv:gr-qc/9712019,
  §3.2, pp. 72–73. [ref: Carroll1997]
* J. Sbierski, *On the existence of a maximal Cauchy development for the
  Einstein equations — a dezornification*, arXiv:1309.7591, §2. [ref: sbierski_2013]

-/
@[expose] public section

namespace GeneralRelativity

namespace Bianchi

open CoordinateCurvature Topology Filter

/-! ## A. Partial-derivative calculus and Schwarz symmetry -/

/-- A `C²` field is differentiable on a neighborhood of `x`. -/
lemma eventually_differentiableAt_of_contDiffAt_two {n : ℕ}
    {f : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ} (hf : ContDiffAt ℝ 2 f x) :
    ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ f y := by
  obtain ⟨u, hu, h'u⟩ := hf.contDiffOn (m := 2) le_rfl (by simp)
  rcases mem_nhds_iff.1 hu with ⟨v, vu, v_open, xv⟩
  filter_upwards [v_open.mem_nhds xv] with y hy
  exact ((h'u.mono vu y hy).contDiffAt (v_open.mem_nhds hy)).differentiableAt two_ne_zero

/-- The coordinate partial derivative of a `C²` field is `C¹` at `x`. -/
lemma contDiffAt_one_pd {n : ℕ} {f : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ}
    (hf : ContDiffAt ℝ 2 f x) (ν : Fin n) :
    ContDiffAt ℝ 1 (CoordinateCurvature.coordDeriv ν f) x := by
  have hfd : ContDiffAt ℝ 1 (fderiv ℝ f) x :=
    hf.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)
  have hclm : ContDiffAt ℝ 1 (fun y => fderiv ℝ f y (Pi.single ν 1)) x :=
    hfd.clm_apply contDiffAt_const
  have heq : CoordinateCurvature.coordDeriv ν f =ᶠ[𝓝 x] fun y => fderiv ℝ f y (Pi.single ν 1) := by
    filter_upwards [eventually_differentiableAt_of_contDiffAt_two hf] with y hy
    exact coordDeriv_eq_fderiv (μ := ν) hy
  exact hclm.congr_of_eventuallyEq heq

/-! ## B. Covariant derivatives and divergence -/

/-- Covariant derivative of a `(0, 2)` tensor field:
`∇_l T_{ij} = ∂_l T_{ij} - Γ^a_{li} T_{aj} - Γ^a_{lj} T_{ia}`. -/
noncomputable def covDeriv2 {n : ℕ} (g ginv T : (Fin n → ℝ) → Tensor2 n)
    (x : Fin n → ℝ) (l i j : Fin n) : ℝ :=
  CoordinateCurvature.coordDeriv l (fun y => T y i j) x
    - ∑ a, christoffel g ginv x a l i * T x a j
    - ∑ a, christoffel g ginv x a l j * T x i a

/-- Covariant derivative of a `(2, 0)` tensor field:
`∇_l T^{ij} = ∂_l T^{ij} + Γ^i_{la} T^{aj} + Γ^j_{la} T^{ia}`. -/
noncomputable def covDeriv2Up {n : ℕ} (g ginv T : (Fin n → ℝ) → Tensor2 n)
    (x : Fin n → ℝ) (l i j : Fin n) : ℝ :=
  CoordinateCurvature.coordDeriv l (fun y => T y i j) x
    + ∑ a, christoffel g ginv x i l a * T x a j
    + ∑ a, christoffel g ginv x j l a * T x i a

/-- Covariant derivative of the `(1, 3)` Riemann curvature tensor:
`∇_l R^ρ_{σμν} = ∂_l R^ρ_{σμν} + Γ^ρ_{la} R^a_{σμν} - Γ^a_{lσ} R^ρ_{aμν}
  - Γ^a_{lμ} R^ρ_{σaν} - Γ^a_{lν} R^ρ_{σμa}`. -/
noncomputable def covDerivRiemann {n : ℕ} (g ginv : (Fin n → ℝ) → Tensor2 n)
    (x : Fin n → ℝ) (l ρ σ μ ν : Fin n) : ℝ :=
  CoordinateCurvature.coordDeriv l (fun y => riemann g ginv y ρ σ μ ν) x
    + ∑ a, christoffel g ginv x ρ l a * riemann g ginv x a σ μ ν
    - ∑ a, christoffel g ginv x a l σ * riemann g ginv x ρ a μ ν
    - ∑ a, christoffel g ginv x a l μ * riemann g ginv x ρ σ a ν
    - ∑ a, christoffel g ginv x a l ν * riemann g ginv x ρ σ μ a

/-- Covariant divergence of a `(0, 2)` tensor field:
`(∇·T)_j = g^{μν} ∇_μ T_{νj}`. -/
noncomputable def covDiv2 {n : ℕ} (g ginv T : (Fin n → ℝ) → Tensor2 n)
    (x : Fin n → ℝ) (j : Fin n) : ℝ :=
  ∑ μ, ∑ ν, ginv x μ ν * covDeriv2 g ginv T x μ ν j

/-! ## C. Metric compatibility and Riemann symmetries -/

/-- The Christoffel symbols are symmetric in their lower two indices whenever
`g` is symmetric near `x`. -/
lemma christoffel_symm {n : ℕ} (g ginv : (Fin n → ℝ) → Tensor2 n) {x : Fin n → ℝ}
    (hgSymm : ∀ᶠ y in 𝓝 x, ∀ i j, g y i j = g y j i) (k i j : Fin n) :
    christoffel g ginv x k i j = christoffel g ginv x k j i := by
  simp only [christoffel]
  congr 1
  apply Finset.sum_congr rfl
  intro l _
  have hsym : CoordinateCurvature.coordDeriv l (fun y => g y i j) x =
      CoordinateCurvature.coordDeriv l (fun y => g y j i) x :=
    coordDeriv_congr_nhds l x (hgSymm.mono fun y hy => hy i j)
  rw [hsym]
  ring

/-- **General metric compatibility**: `∇_l g_{ij} = 0` in arbitrary dimension
`n`, requiring only local symmetry of `g` and the inverse relation at `x`. -/
lemma metric_compat {n : ℕ} (g ginv : (Fin n → ℝ) → Tensor2 n) {x : Fin n → ℝ}
    (hgSymm : ∀ᶠ y in 𝓝 x, ∀ i j, g y i j = g y j i)
    (hInv : ∀ m j, ∑ a, ginv x a m * g x a j = if m = j then 1 else 0)
    (l i j : Fin n) :
    covDeriv2 g ginv g x l i j = 0 := by
  have hsum : ∀ p q : Fin n,
      (∑ a, christoffel g ginv x a l p * g x a q) =
        (1 / 2) * (CoordinateCurvature.coordDeriv l (fun y => g y p q) x
          + CoordinateCurvature.coordDeriv p (fun y => g y l q) x
          - CoordinateCurvature.coordDeriv q (fun y => g y l p) x) := by
    intro p q
    simp only [christoffel, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    calc
      ∑ m, ∑ a, (1 / 2) * (ginv x a m *
          (CoordinateCurvature.coordDeriv l (fun y => g y p m) x
            + CoordinateCurvature.coordDeriv p (fun y => g y l m) x
            - CoordinateCurvature.coordDeriv m (fun y => g y l p) x)) * g x a q
          = ∑ m, (1 / 2) * (CoordinateCurvature.coordDeriv l (fun y => g y p m) x
            + CoordinateCurvature.coordDeriv p (fun y => g y l m) x
              - CoordinateCurvature.coordDeriv m (fun y => g y l p) x) * (∑ a, ginv x a m
                * g x a q) := by
            apply Finset.sum_congr rfl
            intro m _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro a _
            ring
      _ = ∑ m, (1 / 2) * (CoordinateCurvature.coordDeriv l (fun y => g y p m) x
        + CoordinateCurvature.coordDeriv p (fun y => g y l m) x
            - CoordinateCurvature.coordDeriv m (fun y => g y l p) x) *
            (if m = q then 1 else 0) := by
            apply Finset.sum_congr rfl
            intro m _
            rw [hInv m q]
      _ = (1 / 2) * (CoordinateCurvature.coordDeriv l (fun y => g y p q) x
        + CoordinateCurvature.coordDeriv p (fun y => g y l q) x
            - CoordinateCurvature.coordDeriv q (fun y => g y l p) x) := by
            simp
  have h1 := hsum i j
  have h2 : (∑ a, christoffel g ginv x a l j * g x i a) =
      (1 / 2) * (CoordinateCurvature.coordDeriv l (fun y => g y j i) x
        + CoordinateCurvature.coordDeriv j (fun y => g y l i) x
        - CoordinateCurvature.coordDeriv i (fun y => g y l j) x) := by
    have hg0 : ∀ a b, g x a b = g x b a := hgSymm.self_of_nhds
    have hrewrite : (∑ a, christoffel g ginv x a l j * g x i a) =
        ∑ a, christoffel g ginv x a l j * g x a i := by
      apply Finset.sum_congr rfl
      intro a _
      rw [hg0 i a]
    rw [hrewrite, hsum j i]
  have hpd_sym : CoordinateCurvature.coordDeriv l (fun y => g y j i) x =
      CoordinateCurvature.coordDeriv l (fun y => g y i j) x :=
    coordDeriv_congr_nhds l x (hgSymm.mono fun y hy => hy j i)
  unfold covDeriv2
  rw [h1, h2, hpd_sym]
  ring

/-- The coordinate derivative of the metric, in component form: metric compatibility
`∇_l g_{kj} = 0` solved for `∂_l g_{kj}` gives
`∂_l g_{kj} = ∑_a Γ^a_{lk} g_{aj} + ∑_a Γ^a_{lj} g_{ka}`. -/
lemma coordDeriv_g_eq {n : ℕ} (g ginv : (Fin n → ℝ) → Tensor2 n) {x : Fin n → ℝ}
    (hgSymm : ∀ᶠ y in 𝓝 x, ∀ i j, g y i j = g y j i)
    (hInv : ∀ m j, ∑ a, ginv x a m * g x a j = if m = j then 1 else 0)
    (l k j : Fin n) :
    CoordinateCurvature.coordDeriv l (fun y => g y k j) x =
      (∑ a, christoffel g ginv x a l k * g x a j)
        + ∑ a, christoffel g ginv x a l j * g x k a := by
  have h := metric_compat g ginv hgSymm hInv l k j
  unfold covDeriv2 at h
  linarith

/-- Neighborhood form of `coordDeriv_g_eq`: on a neighborhood of `x`, the coordinate
derivative of the metric equals the Christoffel component expression. -/
lemma coordDeriv_g_eq_nhds {n : ℕ} (g ginv : (Fin n → ℝ) → Tensor2 n) {x : Fin n → ℝ}
    (hgSymm : ∀ᶠ y in 𝓝 x, ∀ i j, g y i j = g y j i)
    (hInv : ∀ᶠ y in 𝓝 x, ∀ m j, ∑ a, ginv y a m * g y a j = if m = j then 1 else 0)
    (a b c : Fin n) :
    (fun y => CoordinateCurvature.coordDeriv c (fun z => g z a b) y) =ᶠ[𝓝 x]
      fun y => (∑ β, christoffel g ginv y β c a * g y β b)
        + ∑ β, christoffel g ginv y β c b * g y a β := by
  have hS : ∀ᶠ y in 𝓝 x, ∀ᶠ z in 𝓝 y, ∀ i j, g z i j = g z j i :=
    eventually_eventually_nhds.mpr hgSymm
  filter_upwards [hS, hInv] with y hyS hyInv
  have h := metric_compat g ginv hyS hyInv c a b
  unfold covDeriv2 at h
  linarith

/-- The coordinate derivative of the inverse metric: differentiating `g * ginv = 1`
and solving for `∂ ginv` gives `∂_l ginv^{ib} = -∑_{j,k} ginv^{ik} (∂_l g_{kj}) ginv^{jb}`. -/
private lemma coordDeriv_ginv_eq {n : ℕ} (g ginv : (Fin n → ℝ) → Tensor2 n) {x : Fin n → ℝ}
    (hInvL : ∀ᶠ y in 𝓝 x, ∀ i j, ∑ k, ginv y i k * g y k j = if i = j then 1 else 0)
    (hInvR : ∀ i j, ∑ k, g x i k * ginv x k j = if i = j then 1 else 0)
    (hgD : ∀ i j, DifferentiableAt ℝ (fun y => g y i j) x)
    (hginvD : ∀ i j, DifferentiableAt ℝ (fun y => ginv y i j) x)
    (l i b : Fin n) :
    CoordinateCurvature.coordDeriv l (fun y => ginv y i b) x =
      -∑ j, ∑ k, ginv x i k * CoordinateCurvature.coordDeriv l (fun y => g y k j) x
        * ginv x j b := by
  have hdiff : ∀ j, ∑ k, (CoordinateCurvature.coordDeriv l (fun y => ginv y i k) x * g x k j
      + ginv x i k * CoordinateCurvature.coordDeriv l (fun y => g y k j) x) = 0 := by
    intro j
    have hconst : CoordinateCurvature.coordDeriv l (fun y => ∑ k, ginv y i k * g y k j) x = 0 := by
      rw [coordDeriv_congr_nhds l x (hInvL.mono fun y hy => hy i j)]
      exact coordDeriv_const l _ x
    rw [coordDeriv_sum l (fun k y => ginv y i k * g y k j) x
      (fun k => slice_differentiableAt l ((hginvD i k).mul (hgD k j)))] at hconst
    rw [← hconst]
    apply Finset.sum_congr rfl
    intro k _
    exact (coordDeriv_mul l x (slice_differentiableAt l (hginvD i k))
      (slice_differentiableAt l (hgD k j))).symm
  have h1 : CoordinateCurvature.coordDeriv l (fun y => ginv y i b) x =
      ∑ k, CoordinateCurvature.coordDeriv l (fun y => ginv y i k) x * (∑ j, g x k j
        * ginv x j b) := by
    simp [hInvR]
  rw [h1]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  have hstep : ∀ j, (∑ k, CoordinateCurvature.coordDeriv l (fun y => ginv y i k) x * (g x k j
    * ginv x j b)) =
      -(∑ k, ginv x i k *
        CoordinateCurvature.coordDeriv l (fun y => g y k j) x * ginv x j b) := by
    intro j
    have hd := hdiff j
    have hmul : (∑ k, (CoordinateCurvature.coordDeriv l (fun y => ginv y i k) x * g x k j
        + ginv x i k * CoordinateCurvature.coordDeriv l (fun y => g y k j) x) * ginv x j b)
          = 0 := by
      rw [← Finset.sum_mul, hd, zero_mul]
    have hsplit : (∑ k, (CoordinateCurvature.coordDeriv l (fun y => ginv y i k) x * g x k j
        + ginv x i k * CoordinateCurvature.coordDeriv l (fun y => g y k j) x) * ginv x j b) =
        (∑ k, CoordinateCurvature.coordDeriv l (fun y => ginv y i k) x * (g x k j * ginv x j b))
          + ∑ k, ginv x i k * CoordinateCurvature.coordDeriv l (fun y => g y k j) x
            * ginv x j b := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k _
      ring
    linarith
  simp_rw [hstep, Finset.sum_neg_distrib]

/-- **Inverse metric compatibility**: `∇_l g^{ij} = 0`. -/
lemma inv_metric_compat {n : ℕ} (g ginv : (Fin n → ℝ) → Tensor2 n) {x : Fin n → ℝ}
    (hgSymm : ∀ᶠ y in 𝓝 x, ∀ i j, g y i j = g y j i)
    (hInvL : ∀ᶠ y in 𝓝 x, ∀ i j, ∑ k, ginv y i k * g y k j = if i = j then 1 else 0)
    (hInvR : ∀ i j, ∑ k, g x i k * ginv x k j = if i = j then 1 else 0)
    (hginvSymm : ∀ i j, ginv x i j = ginv x j i)
    (hgD : ∀ i j, DifferentiableAt ℝ (fun y => g y i j) x)
    (hginvD : ∀ i j, DifferentiableAt ℝ (fun y => ginv y i j) x)
    (l i b : Fin n) :
    covDeriv2Up g ginv ginv x l i b = 0 := by
  have hInvAt : ∀ m j, ∑ a, ginv x a m * g x a j = if m = j then 1 else 0 := by
    intro m j
    have h0 := hInvL.self_of_nhds m j
    simpa [hginvSymm] using h0
  have hpd_ginv : CoordinateCurvature.coordDeriv l (fun y => ginv y i b) x =
      -∑ j, ∑ k, ginv x i k * CoordinateCurvature.coordDeriv l (fun y => g y k j) x
        * ginv x j b := coordDeriv_ginv_eq g ginv hInvL hInvR hgD hginvD l i b
  have hmc : ∀ k j, CoordinateCurvature.coordDeriv l (fun y => g y k j) x =
      (∑ a, christoffel g ginv x a l k * g x a j)
        + ∑ a, christoffel g ginv x a l j * g x k a :=
    coordDeriv_g_eq g ginv hgSymm hInvAt l
  have hterm1 : (∑ j, ∑ k, ginv x i k * (∑ a, christoffel g ginv x a l k * g x a j) * ginv x j b) =
      ∑ k, christoffel g ginv x b l k * ginv x i k := by
    calc
      ∑ j, ∑ k, ginv x i k * (∑ a, christoffel g ginv x a l k * g x a j) * ginv x j b
          = ∑ k, ∑ a, ginv x i k * christoffel g ginv x a l k *
              (∑ j, g x a j * ginv x j b) := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro k _
            simp_rw [Finset.mul_sum, Finset.sum_mul]
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro a _
            apply Finset.sum_congr rfl
            intro j _
            ring
      _ = ∑ k, christoffel g ginv x b l k * ginv x i k := by
            apply Finset.sum_congr rfl
            intro k _
            simp_rw [hInvR]
            simp [mul_comm]
  have hterm2 : (∑ j, ∑ k, ginv x i k * (∑ a, christoffel g ginv x a l j * g x k a) * ginv x j b) =
      ∑ j, christoffel g ginv x i l j * ginv x j b := by
    calc
      ∑ j, ∑ k, ginv x i k * (∑ a, christoffel g ginv x a l j * g x k a) * ginv x j b
          = ∑ j, ∑ a, christoffel g ginv x a l j * ginv x j b *
              (∑ k, ginv x i k * g x k a) := by
            apply Finset.sum_congr rfl
            intro j _
            simp_rw [Finset.mul_sum, Finset.sum_mul]
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro a _
            apply Finset.sum_congr rfl
            intro k _
            ring
      _ = ∑ j, christoffel g ginv x i l j * ginv x j b := by
            apply Finset.sum_congr rfl
            intro j _
            simp_rw [hInvL.self_of_nhds]
            simp
  unfold covDeriv2Up
  rw [hpd_ginv]
  have hsplit : (∑ j, ∑ k, ginv x i k * CoordinateCurvature.coordDeriv l (fun y => g y k j) x
    * ginv x j b) =
      (∑ j, ∑ k, ginv x i k * (∑ a, christoffel g ginv x a l k * g x a j) * ginv x j b)
        + ∑ j, ∑ k, ginv x i k * (∑ a, christoffel g ginv x a l j * g x k a) * ginv x j b := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    rw [hmc k j]
    ring
  rw [hsplit, hterm1, hterm2]
  ring

/-- Antisymmetry of the Riemann tensor in its last two indices. -/
lemma riemann_skew_last {n : ℕ} (g ginv : (Fin n → ℝ) → Tensor2 n)
    (x : Fin n → ℝ) (ρ σ μ ν : Fin n) :
    riemann g ginv x ρ σ μ ν = -riemann g ginv x ρ σ ν μ := by
  unfold riemann
  have hsum : (∑ l, (christoffel g ginv x ρ μ l * christoffel g ginv x l ν σ
      - christoffel g ginv x ρ ν l * christoffel g ginv x l μ σ)) =
      -(∑ l, (christoffel g ginv x ρ ν l * christoffel g ginv x l μ σ
        - christoffel g ginv x ρ μ l * christoffel g ginv x l ν σ)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro l _
    ring
  rw [hsum]
  ring

/-- The second coordinate derivative of the metric, in component form: differentiating
`∂_q g_{ασ} = ∑_β Γ^β_{qα} g_{βσ} + ∑_β Γ^β_{qσ} g_{αβ}` once more and applying the
product rule gives `∂_p ∂_q g_{ασ}` as a sum of derivative-of-Christoffel and
Christoffel-squared terms. -/
lemma coordDeriv_coordDeriv_g {n : ℕ} (g ginv : (Fin n → ℝ) → Tensor2 n) {x : Fin n → ℝ}
    (hgSymm : ∀ᶠ y in 𝓝 x, ∀ i j, g y i j = g y j i)
    (hInv : ∀ᶠ y in 𝓝 x, ∀ m j, ∑ a, ginv y a m * g y a j = if m = j then 1 else 0)
    (hgC2 : ∀ i j, ContDiffAt ℝ 2 (fun y => g y i j) x)
    (hΓD : ∀ k i j, DifferentiableAt ℝ (fun y => christoffel g ginv y k i j) x)
    (α σ p q : Fin n) :
    CoordinateCurvature.coordDeriv p (CoordinateCurvature.coordDeriv q (fun z => g z α σ)) x =
      (∑ β, CoordinateCurvature.coordDeriv p (fun y => christoffel g ginv y β q α) x * g x β σ)
        + (∑ β, CoordinateCurvature.coordDeriv p (fun y => christoffel g ginv y β q σ) x * g x α β)
        + (∑ β, ∑ γ, christoffel g ginv x β q α * christoffel g ginv x γ p β * g x γ σ)
        + (∑ β, ∑ γ, christoffel g ginv x β q α * christoffel g ginv x γ p σ * g x β γ)
        + (∑ β, ∑ γ, christoffel g ginv x β q σ * christoffel g ginv x γ p α * g x γ β)
        + (∑ β, ∑ γ, christoffel g ginv x β q σ * christoffel g ginv x γ p β * g x α γ) := by
  have hgD : ∀ i j, DifferentiableAt ℝ (fun y => g y i j) x :=
    fun i j => (hgC2 i j).differentiableAt two_ne_zero
  have hmc_nhds := coordDeriv_g_eq_nhds g ginv hgSymm hInv
  rw [coordDeriv_congr_nhds p x (hmc_nhds α σ q)]
  have h1 : DifferentiableAt ℝ (fun y => ∑ β, christoffel g ginv y β q α * g y β σ) x :=
    DifferentiableAt.fun_sum fun β _ => (hΓD β q α).mul (hgD β σ)
  have h2 : DifferentiableAt ℝ (fun y => ∑ β, christoffel g ginv y β q σ * g y α β) x :=
    DifferentiableAt.fun_sum fun β _ => (hΓD β q σ).mul (hgD α β)
  rw [coordDeriv_add p x (slice_differentiableAt p h1) (slice_differentiableAt p h2),
    coordDeriv_sum p (fun β y => christoffel g ginv y β q α * g y β σ) x
      (fun β => slice_differentiableAt p ((hΓD β q α).fun_mul (hgD β σ))),
    coordDeriv_sum p (fun β y => christoffel g ginv y β q σ * g y α β) x
      (fun β => slice_differentiableAt p ((hΓD β q σ).fun_mul (hgD α β)))]
  have hm1 : ∀ β, CoordinateCurvature.coordDeriv p (fun y => christoffel g ginv y β q α
    * g y β σ) x =
      CoordinateCurvature.coordDeriv p (fun y => christoffel g ginv y β q α) x * g x β σ +
        christoffel g ginv x β q α *
          ((∑ γ, christoffel g ginv x γ p β * g x γ σ) +
            ∑ γ, christoffel g ginv x γ p σ * g x β γ) := by
    intro β
    have hβ : CoordinateCurvature.coordDeriv p (fun y => g y β σ) x =
        (∑ γ, christoffel g ginv x γ p β * g x γ σ) +
          ∑ γ, christoffel g ginv x γ p σ * g x β γ := (hmc_nhds β σ p).self_of_nhds
    rw [coordDeriv_mul p x (slice_differentiableAt p (hΓD β q α))
      (slice_differentiableAt p (hgD β σ)), hβ]
  have hm2 : ∀ β, CoordinateCurvature.coordDeriv p (fun y => christoffel g ginv y β q σ
    * g y α β) x =
      CoordinateCurvature.coordDeriv p (fun y => christoffel g ginv y β q σ) x * g x α β +
        christoffel g ginv x β q σ *
          ((∑ γ, christoffel g ginv x γ p α * g x γ β) +
            ∑ γ, christoffel g ginv x γ p β * g x α γ) := by
    intro β
    have hβ : CoordinateCurvature.coordDeriv p (fun y => g y α β) x =
        (∑ γ, christoffel g ginv x γ p α * g x γ β) +
          ∑ γ, christoffel g ginv x γ p β * g x α γ := (hmc_nhds α β p).self_of_nhds
    rw [coordDeriv_mul p x (slice_differentiableAt p (hΓD β q σ))
      (slice_differentiableAt p (hgD α β)), hβ]
  simp_rw [hm1, hm2, mul_add, Finset.mul_sum, Finset.sum_add_distrib]
  simp_rw [mul_assoc]
  ring

/-- **Skew-symmetry of the lowered Riemann tensor in its first pair**:
`R_{ασμν} + R_{σαμν} = 0`, derived from `∂_μ ∂_ν g_{ασ} = ∂_ν ∂_μ g_{ασ}` and
metric compatibility.  See arXiv:gr-qc/9712019, p. 72. [ref: Carroll1997, p. 72] -/
lemma riemann_lower_skew_first {n : ℕ} (g ginv : (Fin n → ℝ) → Tensor2 n)
    {x : Fin n → ℝ}
    (hgSymm : ∀ᶠ y in 𝓝 x, ∀ i j, g y i j = g y j i)
    (hInv : ∀ᶠ y in 𝓝 x, ∀ m j, ∑ a, ginv y a m * g y a j = if m = j then 1 else 0)
    (hgC2 : ∀ i j, ContDiffAt ℝ 2 (fun y => g y i j) x)
    (hΓD : ∀ k i j, DifferentiableAt ℝ (fun y => christoffel g ginv y k i j) x)
    (α σ μ ν : Fin n) :
    (∑ β, g x α β * riemann g ginv x β σ μ ν) +
      (∑ β, g x σ β * riemann g ginv x β α μ ν) = 0 := by
  have hcomm : CoordinateCurvature.coordDeriv μ (CoordinateCurvature.coordDeriv ν (fun z => g z α
    σ)) x - CoordinateCurvature.coordDeriv ν (CoordinateCurvature.coordDeriv μ (fun z => g z α σ)) x
    = 0 := by
    rw [coordDeriv_comm μ ν (hgC2 α σ)]
    ring
  have hg0 : ∀ a b, g x a b = g x b a := hgSymm.self_of_nhds
  have hcross1 :
      (∑ β, ∑ γ, christoffel g ginv x β ν α * christoffel g ginv x γ μ σ * g x β γ) =
      (∑ β, ∑ γ, christoffel g ginv x β μ σ * christoffel g ginv x γ ν α * g x γ β) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro β _
    apply Finset.sum_congr rfl
    intro γ _
    rw [hg0 γ β]
    ring
  have hcross2 :
      (∑ β, ∑ γ, christoffel g ginv x β ν σ * christoffel g ginv x γ μ α * g x γ β) =
      (∑ β, ∑ γ, christoffel g ginv x β μ α * christoffel g ginv x γ ν σ * g x β γ) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro β _
    apply Finset.sum_congr rfl
    intro γ _
    ring
  have hswap1 :
      (∑ β, ∑ γ, christoffel g ginv x β ν α * christoffel g ginv x γ μ β * g x γ σ) =
      (∑ β, g x σ β * ∑ γ, christoffel g ginv x β μ γ * christoffel g ginv x γ ν α) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro β _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro γ _
    rw [hg0 σ β]
    ring
  have hswap2 :
      (∑ β, ∑ γ, christoffel g ginv x β μ α * christoffel g ginv x γ ν β * g x γ σ) =
      (∑ β, g x σ β * ∑ γ, christoffel g ginv x β ν γ * christoffel g ginv x γ μ α) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro β _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro γ _
    rw [hg0 σ β]
    ring
  have hswap3 :
      (∑ β, ∑ γ, christoffel g ginv x β ν σ * christoffel g ginv x γ μ β * g x α γ) =
      (∑ β, g x α β * ∑ γ, christoffel g ginv x β μ γ * christoffel g ginv x γ ν σ) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro β _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro γ _
    ring
  have hswap4 :
      (∑ β, ∑ γ, christoffel g ginv x β μ σ * christoffel g ginv x γ ν β * g x α γ) =
      (∑ β, g x α β * ∑ γ, christoffel g ginv x β ν γ * christoffel g ginv x γ μ σ) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro β _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro γ _
    ring
  rw [coordDeriv_coordDeriv_g g ginv hgSymm hInv hgC2 hΓD α σ μ ν,
    coordDeriv_coordDeriv_g g ginv hgSymm hInv hgC2 hΓD α σ ν μ,
    hcross1, hcross2, hswap1, hswap2, hswap3, hswap4] at hcomm
  have htarget :
      (∑ β, g x α β * riemann g ginv x β σ μ ν) +
        (∑ β, g x σ β * riemann g ginv x β α μ ν) =
      (∑ β, CoordinateCurvature.coordDeriv μ (fun y => christoffel g ginv y β ν α) x * g x β σ)
        + (∑ β, CoordinateCurvature.coordDeriv μ (fun y => christoffel g ginv y β ν σ) x * g x α β)
        + (∑ β, g x σ β * ∑ γ, christoffel g ginv x β μ γ * christoffel g ginv x γ ν α)
        + (∑ β, g x α β * ∑ γ, christoffel g ginv x β μ γ * christoffel g ginv x γ ν σ)
        - (∑ β, CoordinateCurvature.coordDeriv ν (fun y => christoffel g ginv y β μ α) x * g x β σ)
        - (∑ β, CoordinateCurvature.coordDeriv ν (fun y => christoffel g ginv y β μ σ) x * g x α β)
        - (∑ β, g x σ β * ∑ γ, christoffel g ginv x β ν γ * christoffel g ginv x γ μ α)
        - (∑ β, g x α β * ∑ γ, christoffel g ginv x β ν γ * christoffel g ginv x γ μ σ) := by
    simp only [riemann, mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Finset.mul_sum]
    have hs1 : ∀ (f : Fin n → ℝ), (∑ β, g x σ β * f β) = ∑ β, f β * g x β σ := by
      intro f
      apply Finset.sum_congr rfl
      intro β _
      rw [hg0 σ β]
      ring
    have ha1 : ∀ (f : Fin n → ℝ), (∑ β, g x α β * f β) = ∑ β, f β * g x α β := by
      intro f
      apply Finset.sum_congr rfl
      intro β _
      ring
    simp_rw [hs1, ha1, ← Finset.mul_sum]
    ring
  rw [htarget]
  linarith

/-- **Pair symmetry from the algebraic Bianchi identity** (MTW four-Bianchi
argument): antisymmetry in both pairs plus
`R_{ijkl} + R_{iklj} + R_{iljk} = 0` implies `R_{ijkl} = R_{klij}`.
See arXiv:gr-qc/9712019, p. 73. [ref: Carroll1997, p. 73] -/
lemma pair_symm_of_skew_bianchi {n : ℕ}
    {R : Fin n → Fin n → Fin n → Fin n → ℝ}
    (hskew_first : ∀ i j k l, R i j k l = -R j i k l)
    (hskew_last : ∀ i j k l, R i j k l = -R i j l k)
    (hbianchi : ∀ i j k l, R i j k l + R i k l j + R i l j k = 0)
    (i j k l : Fin n) : R i j k l = R k l i j := by
  have hcycle : R i j k l = 2 * R k l i j - R i j k l := by
    calc
      R i j k l = -R i j l k := hskew_last i j k l
      _ = R j i l k := by rw [hskew_first i j l k]; ring
      _ = -R j l k i - R j k i l := by
            have h := hbianchi j i l k
            linarith
      _ = R l j k i + R k j i l := by
            rw [hskew_first j l k i, hskew_first j k i l]
            ring
      _ = (-R l k i j - R l i j k) + (-R k i l j - R k l j i) := by
            have h1 := hbianchi l j k i
            have h2 := hbianchi k j i l
            linarith
      _ = 2 * R k l i j + R i l j k + R i k l j := by
            rw [hskew_first l k i j, hskew_first l i j k,
              hskew_first k i l j, hskew_last k l j i]
            ring
      _ = 2 * R k l i j - R i j k l := by
            have h := hbianchi i l j k
            linarith
  linarith

/-- **Algebraic first Bianchi identity for the coordinate Riemann tensor**:
`R^ρ_{σμν} + R^ρ_{μνσ} + R^ρ_{νσμ} = 0`, using symmetry of the Christoffel
symbols in a neighborhood.  See arXiv:gr-qc/9712019, p. 73.
[ref: Carroll1997, p. 73] -/
lemma riemann_bianchi {n : ℕ} (g ginv : (Fin n → ℝ) → Tensor2 n)
    (x : Fin n → ℝ)
    (hΓ : ∀ᶠ y in 𝓝 x, ∀ k i j, christoffel g ginv y k i j =
      christoffel g ginv y k j i)
    (ρ σ μ ν : Fin n) :
    riemann g ginv x ρ σ μ ν + riemann g ginv x ρ μ ν σ
      + riemann g ginv x ρ ν σ μ = 0 := by
  have hd : ∀ a k i j,
      CoordinateCurvature.coordDeriv a (fun y => christoffel g ginv y k i j) x =
        CoordinateCurvature.coordDeriv a (fun y => christoffel g ginv y k j i) x := by
    intro a k i j
    exact coordDeriv_congr_nhds a x (hΓ.mono fun y hy => hy k i j)
  simp only [riemann]
  rw [hd ν ρ μ σ, hd σ ρ ν μ, hd μ ρ σ ν]
  have hxΓ := hΓ.self_of_nhds
  simp_rw [hxΓ]
  set S1 : ℝ := ∑ l, (christoffel g ginv x ρ μ l *
    christoffel g ginv x l σ ν -
    christoffel g ginv x ρ ν l * christoffel g ginv x l σ μ) with hS1
  set S2 : ℝ := ∑ l, (christoffel g ginv x ρ ν l *
    christoffel g ginv x l σ μ -
    christoffel g ginv x ρ σ l * christoffel g ginv x l μ ν) with hS2
  set S3 : ℝ := ∑ l, (christoffel g ginv x ρ σ l *
    christoffel g ginv x l μ ν -
    christoffel g ginv x ρ μ l * christoffel g ginv x l σ ν) with hS3
  have hsum : S1 + S2 + S3 = 0 := by
    rw [hS1, hS2, hS3]
    simp only [← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro l _
    ring
  linear_combination hsum

/-- **Lowered first Bianchi identity**: `R_{ασμν} + R_{αμνσ} + R_{ανσμ} = 0`.
See arXiv:gr-qc/9712019, p. 73. [ref: Carroll1997, p. 73] -/
lemma riemann_lower_bianchi {n : ℕ} (g ginv : (Fin n → ℝ) → Tensor2 n)
    (x : Fin n → ℝ)
    (hΓ : ∀ᶠ y in 𝓝 x, ∀ k i j, christoffel g ginv y k i j =
      christoffel g ginv y k j i)
    (α σ μ ν : Fin n) :
    (∑ β, g x α β * riemann g ginv x β σ μ ν)
      + (∑ β, g x α β * riemann g ginv x β μ ν σ)
      + (∑ β, g x α β * riemann g ginv x β ν σ μ) = 0 := by
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro β _
  have h := riemann_bianchi g ginv x hΓ β σ μ ν
  linear_combination (g x α β) * h

/-- **Pair symmetry of the lowered Riemann tensor**:
`R_{ασμν} = R_{μνασ}`.  See arXiv:gr-qc/9712019, p. 73.
[ref: Carroll1997, p. 73] -/
lemma riemann_lower_pair_symm {n : ℕ} (g ginv : (Fin n → ℝ) → Tensor2 n)
    {x : Fin n → ℝ}
    (hgSymm : ∀ᶠ y in 𝓝 x, ∀ i j, g y i j = g y j i)
    (hInv : ∀ᶠ y in 𝓝 x, ∀ m j, ∑ a, ginv y a m * g y a j = if m = j then 1 else 0)
    (hgC2 : ∀ i j, ContDiffAt ℝ 2 (fun y => g y i j) x)
    (hΓD : ∀ k i j, DifferentiableAt ℝ (fun y => christoffel g ginv y k i j) x)
    (hΓ : ∀ᶠ y in 𝓝 x, ∀ k i j, christoffel g ginv y k i j =
      christoffel g ginv y k j i)
    (α σ μ ν : Fin n) :
    (∑ β, g x α β * riemann g ginv x β σ μ ν) =
      (∑ β, g x μ β * riemann g ginv x β ν α σ) := by
  let R : Fin n → Fin n → Fin n → Fin n → ℝ :=
    fun i j k l => ∑ β, g x i β * riemann g ginv x β j k l
  change R α σ μ ν = R μ ν α σ
  refine pair_symm_of_skew_bianchi ?_ ?_ ?_ α σ μ ν
  · intro i j k l
    have h := riemann_lower_skew_first g ginv hgSymm hInv hgC2 hΓD i j k l
    simp only [R]
    linarith
  · intro i j k l
    simp only [R]
    calc
      (∑ β, g x i β * riemann g ginv x β j k l)
          = ∑ β, g x i β * (-riemann g ginv x β j l k) := by
            apply Finset.sum_congr rfl
            intro β _
            rw [riemann_skew_last]
      _ = -∑ β, g x i β * riemann g ginv x β j l k := by
            simp_rw [mul_neg, Finset.sum_neg_distrib]
  · intro i j k l
    exact riemann_lower_bianchi g ginv x hΓ i j k l

/-! ## D. General Second Bianchi Identity -/

/-- Algebraic core of the second Bianchi identity in arbitrary dimension `n`,
parameterised by `(Γ, dΓ, ddΓ)` with `Γ^k_{ij} = Γ^k_{ji}` and
`ddΓ_{ab} = ddΓ_{ba}`. -/
lemma second_bianchi_of {n : ℕ}
    (Γ : Fin n → Fin n → Fin n → ℝ)
    (dΓ : Fin n → Fin n → Fin n → Fin n → ℝ)
    (ddΓ : Fin n → Fin n → Fin n → Fin n → Fin n → ℝ)
    (hΓ : ∀ k i j, Γ k i j = Γ k j i)
    (hdd : ∀ a b k i j, ddΓ a b k i j = ddΓ b a k i j)
    (l ρ σ μ ν : Fin n) :
    let R : Fin n → Fin n → Fin n → Fin n → ℝ := fun r s m p =>
      dΓ m r p s - dΓ p r m s + ∑ c, (Γ r m c * Γ c p s - Γ r p c * Γ c m s)
    let dR : Fin n → Fin n → Fin n → Fin n → Fin n → ℝ := fun a r s m p =>
      ddΓ a m r p s - ddΓ a p r m s
        + ∑ c, (dΓ a r m c * Γ c p s + Γ r m c * dΓ a c p s
              - dΓ a r p c * Γ c m s - Γ r p c * dΓ a c m s)
    let covR : Fin n → Fin n → Fin n → Fin n → Fin n → ℝ := fun a r s m p =>
      dR a r s m p
        + ∑ k, Γ r a k * R k s m p
        - ∑ k, Γ k a s * R r k m p
        - ∑ k, Γ k a m * R r s k p
        - ∑ k, Γ k a p * R r s m k
    covR l ρ σ μ ν + covR μ ρ σ ν l + covR ν ρ σ l μ = 0 := by
  intro R dR covR
  have hRskew : ∀ r s m p, R r s m p = -R r s p m := by
    intro r s m p
    simp only [R]
    have hs : (∑ c, (Γ r m c * Γ c p s - Γ r p c * Γ c m s)) =
        -(∑ c, (Γ r p c * Γ c m s - Γ r m c * Γ c p s)) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro c _
      ring
    rw [hs]
    ring
  have htors :
      (-(∑ k, Γ k l μ * R ρ σ k ν) - ∑ k, Γ k l ν * R ρ σ μ k) +
      (-(∑ k, Γ k μ ν * R ρ σ k l) - ∑ k, Γ k μ l * R ρ σ ν k) +
      (-(∑ k, Γ k ν l * R ρ σ k μ) - ∑ k, Γ k ν μ * R ρ σ l k) = 0 := by
    have h1 : ∀ a b c : Fin n,
        ∑ k, Γ k b a * R ρ σ c k = -(∑ k, Γ k a b * R ρ σ k c) := by
      intro a b c
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro k _
      rw [hΓ k b a, hRskew ρ σ c k]
      ring
    rw [h1 l μ ν, h1 μ ν l, h1 ν l μ]
    ring
  have hdd_sum :
      (ddΓ l μ ρ ν σ - ddΓ l ν ρ μ σ) +
      (ddΓ μ ν ρ l σ - ddΓ μ l ρ ν σ) +
      (ddΓ ν l ρ μ σ - ddΓ ν μ ρ l σ) = 0 := by
    rw [hdd μ l ρ ν σ, hdd ν μ ρ l σ, hdd l ν ρ μ σ]
    ring
  have hcubic_pair : ∀ a b c : Fin n,
      (∑ k, Γ ρ a k * ∑ m, Γ k b m * Γ m c σ) =
      (∑ k, Γ k c σ * ∑ m, Γ ρ a m * Γ m b k) := by
    intro a b c
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro m _
    ring
  simp only [covR]
  have hcore :
      (dR l ρ σ μ ν + ∑ k, Γ ρ l k * R k σ μ ν - ∑ k, Γ k l σ * R ρ k μ ν) +
      (dR μ ρ σ ν l + ∑ k, Γ ρ μ k * R k σ ν l - ∑ k, Γ k μ σ * R ρ k ν l) +
      (dR ν ρ σ l μ + ∑ k, Γ ρ ν k * R k σ l μ - ∑ k, Γ k ν σ * R ρ k l μ) = 0 := by
    simp only [dR, R, mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rw [hcubic_pair l μ ν, hcubic_pair l ν μ,
        hcubic_pair μ ν l, hcubic_pair μ l ν,
        hcubic_pair ν l μ, hcubic_pair ν μ l]
    have hlin :
        ((∑ c, dΓ l ρ μ c * Γ c ν σ) + (∑ c, Γ ρ μ c * dΓ l c ν σ)
          - (∑ c, dΓ l ρ ν c * Γ c μ σ) - (∑ c, Γ ρ ν c * dΓ l c μ σ)
          + (∑ k, Γ ρ l k * dΓ μ k ν σ) - (∑ k, Γ ρ l k * dΓ ν k μ σ)
          - (∑ k, Γ k l σ * dΓ μ ρ ν k) + (∑ k, Γ k l σ * dΓ ν ρ μ k)) +
        ((∑ c, dΓ μ ρ ν c * Γ c l σ) + (∑ c, Γ ρ ν c * dΓ μ c l σ)
          - (∑ c, dΓ μ ρ l c * Γ c ν σ) - (∑ c, Γ ρ l c * dΓ μ c ν σ)
          + (∑ k, Γ ρ μ k * dΓ ν k l σ) - (∑ k, Γ ρ μ k * dΓ l k ν σ)
          - (∑ k, Γ k μ σ * dΓ ν ρ l k) + (∑ k, Γ k μ σ * dΓ l ρ ν k)) +
        ((∑ c, dΓ ν ρ l c * Γ c μ σ) + (∑ c, Γ ρ l c * dΓ ν c μ σ)
          - (∑ c, dΓ ν ρ μ c * Γ c l σ) - (∑ c, Γ ρ μ c * dΓ ν c l σ)
          + (∑ k, Γ ρ ν k * dΓ l k μ σ) - (∑ k, Γ ρ ν k * dΓ μ k l σ)
          - (∑ k, Γ k ν σ * dΓ l ρ μ k) + (∑ k, Γ k ν σ * dΓ μ ρ l k)) = 0 := by
      have hm : ∀ (f g : Fin n → ℝ), (∑ k, f k * g k) = ∑ k, g k * f k := by
        intro f g
        apply Finset.sum_congr rfl
        intro k _
        ring
      simp_rw [hm (fun k => Γ k l σ), hm (fun k => Γ k μ σ), hm (fun k => Γ k ν σ)]
      ring
    linarith
  linarith

/-- **General Second Bianchi Identity** in arbitrary coordinates and arbitrary
dimension `n`: `∇_l R^ρ_{σμν} + ∇_μ R^ρ_{σνl} + ∇_ν R^ρ_{σlμ} = 0`. -/
lemma second_bianchi {n : ℕ} (g ginv : (Fin n → ℝ) → Tensor2 n) {x : Fin n → ℝ}
    (hgSymm : ∀ᶠ y in 𝓝 x, ∀ i j, g y i j = g y j i)
    (hΓC2 : ∀ k i j, ContDiffAt ℝ 2 (fun y => christoffel g ginv y k i j) x)
    (l ρ σ μ ν : Fin n) :
    covDerivRiemann g ginv x l ρ σ μ ν
      + covDerivRiemann g ginv x μ ρ σ ν l
      + covDerivRiemann g ginv x ν ρ σ l μ = 0 := by
  have hΓD : ∀ k i j, DifferentiableAt ℝ (fun y => christoffel g ginv y k i j) x :=
    fun k i j => (hΓC2 k i j).differentiableAt two_ne_zero
  have hdΓD : ∀ a k i j,
      DifferentiableAt ℝ (fun y => CoordinateCurvature.coordDeriv a (fun z => christoffel g ginv z k
        i j) y) x :=
    fun a k i j => (contDiffAt_one_pd (hΓC2 k i j) a).differentiableAt one_ne_zero
  have hpdR : ∀ a r s m p : Fin n,
      CoordinateCurvature.coordDeriv a (fun y => riemann g ginv y r s m p) x =
        CoordinateCurvature.coordDeriv a (fun y => CoordinateCurvature.coordDeriv m (fun z =>
          christoffel g ginv z r p s) y) x
        - CoordinateCurvature.coordDeriv a (fun y => CoordinateCurvature.coordDeriv p (fun z =>
          christoffel g ginv z r m s) y) x
        + ∑ c, (CoordinateCurvature.coordDeriv a (fun y => christoffel g ginv y r m c) x
          * christoffel g ginv x c p s
              + christoffel g ginv x r m c
                * CoordinateCurvature.coordDeriv a (fun y => christoffel g ginv y c p s) x
              - CoordinateCurvature.coordDeriv a (fun y => christoffel g ginv y r p c) x
                * christoffel g ginv x c m s
              - christoffel g ginv x r p c
                * CoordinateCurvature.coordDeriv a (fun y => christoffel g ginv y c m s) x) := by
    intro a r s m p
    unfold riemann
    have hsub : DifferentiableAt ℝ (fun y =>
        CoordinateCurvature.coordDeriv m (fun z => christoffel g ginv z r p s) y
          - CoordinateCurvature.coordDeriv p (fun z => christoffel g ginv z r m s) y) x :=
      (hdΓD m r p s).sub (hdΓD p r m s)
    have hsum : DifferentiableAt ℝ (fun y =>
        ∑ c, (christoffel g ginv y r m c * christoffel g ginv y c p s
          - christoffel g ginv y r p c * christoffel g ginv y c m s)) x :=
      DifferentiableAt.fun_sum fun c _ =>
        ((hΓD r m c).mul (hΓD c p s)).sub ((hΓD r p c).mul (hΓD c m s))
    rw [coordDeriv_add a x (slice_differentiableAt a hsub) (slice_differentiableAt a hsum),
      coordDeriv_sub a x (slice_differentiableAt a (hdΓD m r p s))
        (slice_differentiableAt a (hdΓD p r m s)),
      coordDeriv_sum a
        (fun c y => christoffel g ginv y r m c * christoffel g ginv y c p s
          - christoffel g ginv y r p c * christoffel g ginv y c m s) x
        (fun c => slice_differentiableAt a
          (((hΓD r m c).fun_mul (hΓD c p s)).fun_sub
            ((hΓD r p c).fun_mul (hΓD c m s))))]
    congr 1
    apply Finset.sum_congr rfl
    intro c _
    rw [coordDeriv_sub a x
        (slice_differentiableAt a ((hΓD r m c).fun_mul (hΓD c p s)))
        (slice_differentiableAt a ((hΓD r p c).fun_mul (hΓD c m s))),
      coordDeriv_mul a x (slice_differentiableAt a (hΓD r m c))
        (slice_differentiableAt a (hΓD c p s)),
      coordDeriv_mul a x (slice_differentiableAt a (hΓD r p c))
        (slice_differentiableAt a (hΓD c m s))]
    ring
  have halg := second_bianchi_of
    (fun k i j => christoffel g ginv x k i j)
    (fun a k i j => CoordinateCurvature.coordDeriv a (fun y => christoffel g ginv y k i j) x)
    (fun a b k i j => CoordinateCurvature.coordDeriv a (fun y => CoordinateCurvature.coordDeriv b
      (fun z => christoffel g ginv z k i j) y) x)
    (fun k i j => christoffel_symm g ginv hgSymm k i j)
    (fun a b k i j => coordDeriv_comm a b (hΓC2 k i j))
    l ρ σ μ ν
  rw [covDerivRiemann, covDerivRiemann, covDerivRiemann]
  rw [hpdR, hpdR, hpdR]
  simpa only [riemann] using halg

end Bianchi
end GeneralRelativity
