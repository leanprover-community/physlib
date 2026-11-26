/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import PhyslibAlpha.Relativity.Metrics.CoordDeriv
public import PhyslibAlpha.Relativity.Metrics.Minkowski
public import PhyslibAlpha.Relativity.Metrics.RiemannFromData
public import PhyslibAlpha.Relativity.Tensors.EinsteinTensor
import Mathlib.Tactic.Ring

/-!

# The differential curvature pipeline

Differential chain from a coordinate metric and inverse `(g, ginv)` through Levi-Civita
Christoffel symbols, Riemann tensor, Ricci tensor, scalar curvature, and Einstein tensor.

## i. Overview

From any coordinate-dependent metric field `g` and inverse `ginv`, `GeneralRelativity.Pipeline`
evaluates the differential chain

`g ↦ ∂g ↦ Γ^k_{ij} ↦ ∂Γ ↦ R^ρ_{σμν} ↦ Ric_{σν} ↦ S ↦ G_{ij}`

and proves that every constant metric has vanishing connection, Riemann, Ricci, scalar, and
Einstein curvature, while equating `riemann` definitionally to `riemannFromData`.

## ii. Key results

- `Pipeline.christoffel`, `Pipeline.christoffel_diag`, `Pipeline.riemann`,
  `Pipeline.ricciTensorOf`, `Pipeline.ricciScalarOf`, `Pipeline.einsteinTensorOf` : coordinate
  differential pipeline from `(g, ginv)` to the Einstein tensor.
- `Pipeline.christoffel_const`, `Pipeline.riemann_const`, `Pipeline.ricciTensorOf_const`,
  `Pipeline.ricciScalarOf_const`, `Pipeline.einsteinTensorOf_const` : vanishing of all pipeline
  outputs for any constant metric.
- `Pipeline.riemann_eq_riemannFromData`, `Pipeline.riemann_eq_riemannFromData_of_eventuallyEq` :
  identification of `riemann` with `riemannFromData`.

## iii. Table of contents

- A. Metric-to-Einstein differential pipeline
- B. Flatness of constant metrics

## iv. References

* R. M. Wald, *General Relativity* (1984), Ch. 3 (Sec. 3.1-3.2). [ref: wald_1984_general_relativity]
* C. W. Misner, K. S. Thorne, and J. A. Wheeler, *Gravitation* (1973), Ch. 8 & Ch. 13.
  [ref: mtw_1973_gravitation]
* B. O'Neill, *Semi-Riemannian Geometry With Applications to Relativity* (1983), Ch. 3.
  [ref: oneill_1983_semi_riemannian]
* S. M. Carroll, *Lecture Notes on General Relativity* (1997), Ch. 3
  (https://arxiv.org/pdf/gr-qc/9712019#page=58). [ref: Carroll1997]
-/

@[expose] public section

namespace GeneralRelativity

namespace Pipeline

/-!

## A. Metric-to-Einstein differential pipeline

The coordinate partial derivatives `coordDeriv` define the Levi-Civita connection `Γ^k_{ij}`,
Riemann curvature `R^ρ_{σμν}`, Ricci tensor, scalar curvature, and Einstein tensor directly from
metric components.

-/

/-- Christoffel symbols of the second kind,
`Γ^k_{ij} = (1/2) g^{kl} (∂_i g_{jl} + ∂_j g_{il} - ∂_l g_{ij})`. -/
noncomputable def christoffel {n : ℕ} (g ginv : (Fin n → ℝ) → Tensor2 n)
    (x : Fin n → ℝ) (k i j : Fin n) : ℝ :=
  (1 / 2) * ∑ l, ginv x k l *
    (coordDeriv i (fun y => g y j l) x + coordDeriv j (fun y => g y i l) x
      - coordDeriv l (fun y => g y i j) x)

/-- For a metric whose inverse is diagonal at a point, the Christoffel contraction collapses to
the single index `l = k`. -/
lemma christoffel_diag {n : ℕ} (g ginv : (Fin n → ℝ) → Tensor2 n) (x : Fin n → ℝ)
    (k i j : Fin n) (hdiag : ∀ l : Fin n, l ≠ k → ginv x k l = 0) :
    christoffel g ginv x k i j =
      (1 / 2) * (ginv x k k *
        (coordDeriv i (fun y => g y j k) x + coordDeriv j (fun y => g y i k) x
          - coordDeriv k (fun y => g y i j) x)) := by
  simp only [christoffel]
  rw [Finset.sum_eq_single k (fun l _ hl => by simp [hdiag l hl]) (by simp)]

/-- The Riemann curvature tensor
`R^ρ_{σμν} = ∂_μ Γ^ρ_{νσ} - ∂_ν Γ^ρ_{μσ} + Γ^ρ_{μλ} Γ^λ_{νσ} - Γ^ρ_{νλ} Γ^λ_{μσ}`. -/
noncomputable def riemann {n : ℕ} (g ginv : (Fin n → ℝ) → Tensor2 n)
    (x : Fin n → ℝ) (ρ σ μ ν : Fin n) : ℝ :=
  coordDeriv μ (fun y => christoffel g ginv y ρ ν σ) x
    - coordDeriv ν (fun y => christoffel g ginv y ρ μ σ) x
    + ∑ l, (christoffel g ginv x ρ μ l * christoffel g ginv x l ν σ
          - christoffel g ginv x ρ ν l * christoffel g ginv x l μ σ)

/-- The coordinate Ricci tensor `Ric_{σν} = ∑ ρ, R^ρ_{σρν}`. -/
noncomputable def ricciTensorOf {n : ℕ} (g ginv : (Fin n → ℝ) → Tensor2 n)
    (x : Fin n → ℝ) (σ ν : Fin n) : ℝ :=
  ∑ ρ, riemann g ginv x ρ σ ρ ν

/-- The coordinate scalar curvature `S = ∑ σ ν, g^{σν} Ric_{σν}`. -/
noncomputable def ricciScalarOf {n : ℕ} (g ginv : (Fin n → ℝ) → Tensor2 n)
    (x : Fin n → ℝ) : ℝ :=
  ∑ σ, ∑ ν, ginv x σ ν * ricciTensorOf g ginv x σ ν

/-- The coordinate Einstein tensor `G_{ij} = Ric_{ij} - (1/2) S g_{ij}`. -/
noncomputable def einsteinTensorOf {n : ℕ} (g ginv : (Fin n → ℝ) → Tensor2 n)
    (x : Fin n → ℝ) (i j : Fin n) : ℝ :=
  ricciTensorOf g ginv x i j - (1 / 2) * ricciScalarOf g ginv x * g x i j

/-- Feeding `riemannFromData` the metric's actual partial derivatives of `christoffel` reproduces
`riemann` definitionally. -/
lemma riemann_eq_riemannFromData {n : ℕ} (g ginv : (Fin n → ℝ) → Tensor2 n)
    (x : Fin n → ℝ) (ρ σ μ ν : Fin n) :
    riemann g ginv x ρ σ μ ν =
      riemannFromData (christoffel g ginv)
        (fun μ y a b c => coordDeriv μ (fun z => christoffel g ginv z a b c) y)
        x ρ σ μ ν :=
  rfl

/-- Transport `Pipeline.riemann` to `riemannFromData` using local agreement of Christoffel
symbols around a point and matching coordinate partial derivatives at that point. -/
lemma riemann_eq_riemannFromData_of_eventuallyEq {n : ℕ} (g ginv : (Fin n → ℝ) → Tensor2 n)
    (G : (Fin n → ℝ) → Fin n → Fin n → Fin n → ℝ)
    (dG : Fin n → (Fin n → ℝ) → Fin n → Fin n → Fin n → ℝ) (x : Fin n → ℝ)
    (hG_eq : ∀ a b c, (fun y => christoffel g ginv y a b c) =ᶠ[nhds x] fun y => G y a b c)
    (hdG : ∀ μ a b c, coordDeriv μ (fun y => G y a b c) x = dG μ x a b c)
    (ρ σ μ ν : Fin n) :
    riemann g ginv x ρ σ μ ν = riemannFromData G dG x ρ σ μ ν := by
  rw [riemann_eq_riemannFromData]
  simp only [riemannFromData, coordDeriv_congr_nhds _ x (hG_eq _ _ _), hdG,
    (hG_eq _ _ _).eq_of_nhds]

/-!

## B. Flatness of constant metrics

When all metric components are constant across spacetime, every partial derivative vanishes and the
pipeline automatically produces zero connection, Riemann, Ricci, and Einstein curvature.

-/

/-- A constant metric has vanishing Christoffel symbols at every point. -/
lemma christoffel_const {n : ℕ} (g ginv : (Fin n → ℝ) → Tensor2 n) (G : Tensor2 n)
    (hg : ∀ x, g x = G) (x : Fin n → ℝ) (k i j : Fin n) :
    christoffel g ginv x k i j = 0 := by
  have hpd : ∀ (μ a b : Fin n), coordDeriv μ (fun y => g y a b) x = 0 := by
    intro μ a b
    rw [coordDeriv_congr μ x (fun y => by rw [hg y])]
    exact coordDeriv_const μ (G a b) x
  simp only [christoffel]
  rw [Finset.sum_eq_zero (fun l _ => by rw [hpd i j l, hpd j i l, hpd l i j]; ring)]
  ring

/-- A constant metric has zero Riemann curvature at every point. -/
lemma riemann_const {n : ℕ} (g ginv : (Fin n → ℝ) → Tensor2 n) (G : Tensor2 n)
    (hg : ∀ x, g x = G) (x : Fin n → ℝ) (ρ σ μ ν : Fin n) :
    riemann g ginv x ρ σ μ ν = 0 := by
  have hc := fun y => christoffel_const g ginv G hg y
  have h1 : coordDeriv μ (fun y => christoffel g ginv y ρ ν σ) x = 0 := by
    rw [coordDeriv_congr μ x (fun y => hc y ρ ν σ)]
    exact coordDeriv_const μ 0 x
  have h2 : coordDeriv ν (fun y => christoffel g ginv y ρ μ σ) x = 0 := by
    rw [coordDeriv_congr ν x (fun y => hc y ρ μ σ)]
    exact coordDeriv_const ν 0 x
  have h3 : (∑ l, (christoffel g ginv x ρ μ l * christoffel g ginv x l ν σ
              - christoffel g ginv x ρ ν l * christoffel g ginv x l μ σ)) = 0 := by
    apply Finset.sum_eq_zero
    intro l _
    rw [hc x ρ μ l, hc x ρ ν l, hc x l ν σ, hc x l μ σ]
    ring
  rw [riemann, h1, h2, h3]
  ring

/-- A constant metric is Ricci flat, as computed by the pipeline. -/
lemma ricciTensorOf_const {n : ℕ} (g ginv : (Fin n → ℝ) → Tensor2 n) (G : Tensor2 n)
    (hg : ∀ x, g x = G) (x : Fin n → ℝ) (σ ν : Fin n) :
    ricciTensorOf g ginv x σ ν = 0 := by
  simp only [ricciTensorOf]
  apply Finset.sum_eq_zero
  intro ρ _
  exact riemann_const g ginv G hg x ρ σ ρ ν

/-- A constant metric has zero scalar curvature. -/
lemma ricciScalarOf_const {n : ℕ} (g ginv : (Fin n → ℝ) → Tensor2 n) (G : Tensor2 n)
    (hg : ∀ x, g x = G) (x : Fin n → ℝ) : ricciScalarOf g ginv x = 0 := by
  simp only [ricciScalarOf]
  apply Finset.sum_eq_zero
  intro σ _
  apply Finset.sum_eq_zero
  intro ν _
  rw [ricciTensorOf_const g ginv G hg x σ ν]
  ring

/-- A constant metric is a vacuum solution of the Einstein equations (`G_{ij} = 0`), as computed
by the pipeline. -/
lemma einsteinTensorOf_const {n : ℕ} (g ginv : (Fin n → ℝ) → Tensor2 n) (G : Tensor2 n)
    (hg : ∀ x, g x = G) (x : Fin n → ℝ) (i j : Fin n) :
    einsteinTensorOf g ginv x i j = 0 := by
  simp only [einsteinTensorOf]
  rw [ricciTensorOf_const g ginv G hg x i j, ricciScalarOf_const g ginv G hg x]
  ring

end Pipeline

end GeneralRelativity
