/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import PhyslibAlpha.Relativity.General.Basic
import Mathlib.Tactic.Ring

/-!

# The metric to Christoffel to Riemann coordinate pipeline

Coordinate-chart pipeline computing Christoffel symbols, Riemann, Ricci, scalar, and Einstein
tensors directly from metric component fields.

## i. Overview

Given a metric `g : (Fin n → ℝ) → Tensor2 n` and its inverse `ginv` as functions of coordinates
`x : Fin n → ℝ`, this module defines coordinate partial derivatives `pd μ f x` along each
coordinate axis and builds the full differential chain:

`g ↦ ∂g ↦ Γ^k_{ij} ↦ ∂Γ ↦ R^ρ_{σμν} ↦ Ric_{σν} ↦ S ↦ G_{ij}`.

It also provides `riemannFromData`, taking the Christoffel symbols and their partial derivatives
as explicit parameters (which equals `riemann` definitionally when fed `christoffel` and its
coordinate partial derivatives), and proves that every constant metric — and in particular
Minkowski spacetime `minkowskiG` — has vanishing Christoffel symbols, curvature, Ricci tensor,
scalar curvature, and Einstein tensor as computed outputs of the pipeline.

## ii. Key results

- `pd` : coordinate partial derivative along index `μ`.
- `christoffel`, `riemann`, `ricciOf`, `scalarOf`, `einsteinOf` : coordinate pipeline from
  metric fields to the Einstein tensor.
- `christoffel_const`, `riemann_const`, `ricciOf_const`, `scalarOf_const`, `einsteinOf_const` :
  vanishing of all pipeline outputs for any constant metric.
- `minkowski_christoffel`, `minkowski_riemann`, `minkowski_einstein` : Minkowski spacetime as a
  computed vacuum solution.
- `riemannFromData`, `riemann_eq_riemannFromData` : data-parameterised Riemann evaluator and
  definitional equality with `riemann`.

## iii. Table of contents

- A. Coordinate partial derivatives and metric pipeline
- B. Flatness of constant metrics
- C. Minkowski spacetime as a computed vacuum solution
- D. Curvature from Christoffel data

## iv. References

* None.

-/

@[expose] public section

namespace GeneralRelativity

namespace Pipeline

/-!

## A. Coordinate partial derivatives and metric pipeline

-/

/-- The partial derivative of a scalar field along the coordinate `μ`: the derivative of
`s ↦ f (Function.update x μ s)` at `x μ`. -/
noncomputable def pd {n : ℕ} (μ : Fin n) (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : ℝ :=
  deriv (fun s : ℝ => f (Function.update x μ s)) (x μ)

/-- The coordinate partial derivative of a constant field vanishes. -/
lemma pd_const {n : ℕ} (μ : Fin n) (c : ℝ) (x : Fin n → ℝ) :
    pd μ (fun _ => c) x = 0 := by
  simp [pd]

/-- `pd` depends only on the pointwise values of the field. -/
lemma pd_congr {n : ℕ} (μ : Fin n) {f g : (Fin n → ℝ) → ℝ} (x : Fin n → ℝ)
    (h : ∀ y, f y = g y) : pd μ f x = pd μ g x := by
  simp only [pd]
  exact congrArg (fun F => deriv F (x μ)) (funext fun s => h _)

/-- Christoffel symbols of the second kind,
`Γ^k_{ij} = (1/2) g^{kl} (∂_i g_{jl} + ∂_j g_{il} - ∂_l g_{ij})`, at `x`. -/
noncomputable def christoffel {n : ℕ} (g ginv : (Fin n → ℝ) → Tensor2 n)
    (x : Fin n → ℝ) (k i j : Fin n) : ℝ :=
  (1 / 2) * ∑ l, ginv x k l *
    (pd i (fun y => g y j l) x + pd j (fun y => g y i l) x
      - pd l (fun y => g y i j) x)

/-- The Riemann curvature tensor
`R^ρ_{σμν} = ∂_μ Γ^ρ_{νσ} - ∂_ν Γ^ρ_{μσ} + Γ^ρ_{μλ} Γ^λ_{νσ} - Γ^ρ_{νλ} Γ^λ_{μσ}`. -/
noncomputable def riemann {n : ℕ} (g ginv : (Fin n → ℝ) → Tensor2 n)
    (x : Fin n → ℝ) (ρ σ μ ν : Fin n) : ℝ :=
  pd μ (fun y => christoffel g ginv y ρ ν σ) x
    - pd ν (fun y => christoffel g ginv y ρ μ σ) x
    + ∑ l, (christoffel g ginv x ρ μ l * christoffel g ginv x l ν σ
          - christoffel g ginv x ρ ν l * christoffel g ginv x l μ σ)

/-- The coordinate Ricci tensor `Ric_{σν} = ∑ ρ, R^ρ_{σρν}`. -/
noncomputable def ricciOf {n : ℕ} (g ginv : (Fin n → ℝ) → Tensor2 n)
    (x : Fin n → ℝ) (σ ν : Fin n) : ℝ :=
  ∑ ρ, riemann g ginv x ρ σ ρ ν

/-- The coordinate scalar curvature `S = ∑ σ ν, g^{σν} Ric_{σν}`. -/
noncomputable def scalarOf {n : ℕ} (g ginv : (Fin n → ℝ) → Tensor2 n)
    (x : Fin n → ℝ) : ℝ :=
  ∑ σ, ∑ ν, ginv x σ ν * ricciOf g ginv x σ ν

/-- The coordinate Einstein tensor `G_{ij} = Ric_{ij} - (1/2) S g_{ij}`. -/
noncomputable def einsteinOf {n : ℕ} (g ginv : (Fin n → ℝ) → Tensor2 n)
    (x : Fin n → ℝ) (i j : Fin n) : ℝ :=
  ricciOf g ginv x i j - (1 / 2) * scalarOf g ginv x * g x i j

/-!

## B. Flatness of constant metrics

-/

/-- A constant metric has vanishing Christoffel symbols at every point. -/
lemma christoffel_const {n : ℕ} (g ginv : (Fin n → ℝ) → Tensor2 n) (G : Tensor2 n)
    (hg : ∀ x, g x = G) (x : Fin n → ℝ) (k i j : Fin n) :
    christoffel g ginv x k i j = 0 := by
  have hpd : ∀ (μ a b : Fin n), pd μ (fun y => g y a b) x = 0 := by
    intro μ a b
    rw [pd_congr μ x (fun y => by rw [hg y])]
    exact pd_const μ (G a b) x
  simp only [christoffel]
  rw [Finset.sum_eq_zero (fun l _ => by rw [hpd i j l, hpd j i l, hpd l i j]; ring)]
  ring

/-- A constant metric has zero Riemann curvature at every point. -/
lemma riemann_const {n : ℕ} (g ginv : (Fin n → ℝ) → Tensor2 n) (G : Tensor2 n)
    (hg : ∀ x, g x = G) (x : Fin n → ℝ) (ρ σ μ ν : Fin n) :
    riemann g ginv x ρ σ μ ν = 0 := by
  have hc := fun y => christoffel_const g ginv G hg y
  have h1 : pd μ (fun y => christoffel g ginv y ρ ν σ) x = 0 := by
    rw [pd_congr μ x (fun y => hc y ρ ν σ)]
    exact pd_const μ 0 x
  have h2 : pd ν (fun y => christoffel g ginv y ρ μ σ) x = 0 := by
    rw [pd_congr ν x (fun y => hc y ρ μ σ)]
    exact pd_const ν 0 x
  have h3 : (∑ l, (christoffel g ginv x ρ μ l * christoffel g ginv x l ν σ
              - christoffel g ginv x ρ ν l * christoffel g ginv x l μ σ)) = 0 := by
    apply Finset.sum_eq_zero
    intro l _
    rw [hc x ρ μ l, hc x ρ ν l, hc x l ν σ, hc x l μ σ]
    ring
  rw [riemann, h1, h2, h3]
  ring

/-- A constant metric is Ricci flat, as computed by the pipeline. -/
lemma ricciOf_const {n : ℕ} (g ginv : (Fin n → ℝ) → Tensor2 n) (G : Tensor2 n)
    (hg : ∀ x, g x = G) (x : Fin n → ℝ) (σ ν : Fin n) :
    ricciOf g ginv x σ ν = 0 := by
  simp only [ricciOf]
  apply Finset.sum_eq_zero
  intro ρ _
  exact riemann_const g ginv G hg x ρ σ ρ ν

/-- A constant metric has zero scalar curvature. -/
lemma scalarOf_const {n : ℕ} (g ginv : (Fin n → ℝ) → Tensor2 n) (G : Tensor2 n)
    (hg : ∀ x, g x = G) (x : Fin n → ℝ) : scalarOf g ginv x = 0 := by
  simp only [scalarOf]
  apply Finset.sum_eq_zero
  intro σ _
  apply Finset.sum_eq_zero
  intro ν _
  rw [ricciOf_const g ginv G hg x σ ν]
  ring

/-- A constant metric is a vacuum solution of the Einstein equations (`G_{ij} = 0`), as computed
by the pipeline. -/
lemma einsteinOf_const {n : ℕ} (g ginv : (Fin n → ℝ) → Tensor2 n) (G : Tensor2 n)
    (hg : ∀ x, g x = G) (x : Fin n → ℝ) (i j : Fin n) :
    einsteinOf g ginv x i j = 0 := by
  simp only [einsteinOf]
  rw [ricciOf_const g ginv G hg x i j, scalarOf_const g ginv G hg x]
  ring

/-!

## C. Minkowski spacetime as a computed vacuum solution

-/

/-- The Minkowski metric as a field of components on `Fin 4 → ℝ`. -/
noncomputable def minkowskiG : (Fin 4 → ℝ) → Tensor2 4 := fun _ => eta4

/-- The pipeline produces vanishing Christoffel symbols for Minkowski spacetime. -/
lemma minkowski_christoffel (x : Fin 4 → ℝ) (k i j : Fin 4) :
    christoffel minkowskiG minkowskiG x k i j = 0 :=
  christoffel_const minkowskiG minkowskiG eta4 (fun _ => rfl) x k i j

/-- The pipeline produces vanishing Riemann curvature for Minkowski spacetime. -/
lemma minkowski_riemann (x : Fin 4 → ℝ) (ρ σ μ ν : Fin 4) :
    riemann minkowskiG minkowskiG x ρ σ μ ν = 0 :=
  riemann_const minkowskiG minkowskiG eta4 (fun _ => rfl) x ρ σ μ ν

/-- Minkowski spacetime is a vacuum solution of the Einstein equations (`G_{ij} = 0`), computed
from the metric rather than assumed. -/
lemma minkowski_einstein (x : Fin 4 → ℝ) (i j : Fin 4) :
    einsteinOf minkowskiG minkowskiG x i j = 0 :=
  einsteinOf_const minkowskiG minkowskiG eta4 (fun _ => rfl) x i j

/-!

## D. Curvature from Christoffel data

-/

/-- The Riemann tensor evaluated from supplied Christoffel symbols `G` and partial derivatives
`dG`: `R^ρ_{σμν} = ∂_μ Γ^ρ_{νσ} - ∂_ν Γ^ρ_{μσ} + Γ^ρ_{μλ} Γ^λ_{νσ} - Γ^ρ_{νλ} Γ^λ_{μσ}`. -/
noncomputable def riemannFromData {n : ℕ}
    (G : (Fin n → ℝ) → Fin n → Fin n → Fin n → ℝ)
    (dG : Fin n → (Fin n → ℝ) → Fin n → Fin n → Fin n → ℝ)
    (x : Fin n → ℝ) (ρ σ μ ν : Fin n) : ℝ :=
  dG μ x ρ ν σ - dG ν x ρ μ σ
    + ∑ l, (G x ρ μ l * G x l ν σ - G x ρ ν l * G x l μ σ)

/-- `riemannFromData` depends on its derivative argument only at `(μ, ρ, ν, σ)` and
`(ν, ρ, μ, σ)`. -/
lemma riemannFromData_congr {n : ℕ} (G : (Fin n → ℝ) → Fin n → Fin n → Fin n → ℝ)
    {dG dG' : Fin n → (Fin n → ℝ) → Fin n → Fin n → Fin n → ℝ}
    (x : Fin n → ℝ) (ρ σ μ ν : Fin n)
    (h1 : dG μ x ρ ν σ = dG' μ x ρ ν σ) (h2 : dG ν x ρ μ σ = dG' ν x ρ μ σ) :
    riemannFromData G dG x ρ σ μ ν = riemannFromData G dG' x ρ σ μ ν := by
  simp only [riemannFromData, h1, h2]

/-- Feeding `riemannFromData` the metric's actual partial derivatives of `christoffel` reproduces
`riemann` definitionally. -/
lemma riemann_eq_riemannFromData {n : ℕ} (g ginv : (Fin n → ℝ) → Tensor2 n)
    (x : Fin n → ℝ) (ρ σ μ ν : Fin n) :
    riemann g ginv x ρ σ μ ν =
      riemannFromData (christoffel g ginv)
        (fun μ y a b c => pd μ (fun z => christoffel g ginv z a b c) y)
        x ρ σ μ ν :=
  rfl

/-- The data form returns zero curvature on Minkowski spacetime. -/
lemma minkowski_riemannFromData (x : Fin 4 → ℝ) (ρ σ μ ν : Fin 4) :
    riemannFromData (christoffel minkowskiG minkowskiG)
      (fun μ y a b c => pd μ (fun z => christoffel minkowskiG minkowskiG z a b c) y)
      x ρ σ μ ν = 0 := by
  rw [← riemann_eq_riemannFromData]
  exact minkowski_riemann x ρ σ μ ν

end Pipeline

end GeneralRelativity
