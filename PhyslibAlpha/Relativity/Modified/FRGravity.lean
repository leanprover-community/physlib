/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import PhyslibAlpha.Relativity.Tensors.EinsteinTensor
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!

# `f(R)` gravity and the Starobinsky model

Field equations, trace dynamics, Starobinsky potential, and Einstein-frame slow-roll plateau in
`f(R)` gravity.

## i. Overview

Metric `f(R)` gravity replaces the Einstein–Hilbert Lagrangian `R` by a nonlinear function
`f(R)`, yielding fourth-order metric equations containing a propagating scalar mode `φ = f'(R)`
with mass squared `1 / (3 f''(R))`.

This module defines `FRTheory` (a potential `f` together with its derivative `df = f'`), isolates
the algebraic curvature equations from the fourth-order derivative terms
`-∇_i ∇_j f'(R) + g_{ij} □f'(R)` (which vanish whenever `f'` is constant, i.e., for
constant-scalar or General Relativity solutions), and formalises:

- the algebraic part `FRTheory.algebraicFieldEqn` of the `f(R)` field equation and its reduction to
  `G + Λ g` when `FRTheory.generalRelativity Λ` is chosen (`linear_is_einstein`);
- the `n`-dimensional trace identity `f'(R) R - (n/2) f(R) + (n - 1) □f'`
  (`trace_algebraicFieldEqn`) and its four-dimensional `3 □f'` specialisation
  (`trace_algebraicFieldEqn_four`);
- Starobinsky's `R + α R²` model (`FRTheory.starobinsky α`), its Legendre potential
  `(φ - 1)² / (8 α)`, and the Einstein-frame plateau `U(φ) = (1 - 1/φ)² / (8 α) → 1 / (8 α)` as
  `φ → ∞`.

## ii. Key results

- `FRTheory`, `FRTheory.generalRelativity`, `FRTheory.starobinsky` : `f(R)` gravity model
  specified by `f` and `df`, with General Relativity and Starobinsky instances.
- `FRTheory.algebraicFieldEqn`, `linear_is_einstein` : algebraic `f(R)` equations and recovery of
  `G + Λ g`.
- `trace_algebraicFieldEqn`, `trace_algebraicFieldEqn_four` : trace equation showing the
  propagating scalar mode.
- `starobinskyPotential`, `starobinsky_scalar_inversion`, `starobinskyPotential_eq`,
  `starobinsky_nonconstant_deriv` : Starobinsky `R + α R²` potential and scalar degree of freedom.
- `einsteinFramePotential`, `starobinsky_einsteinFrame_form`, `starobinsky_plateau` :
  Einstein-frame conformal potential and asymptotic slow-roll plateau.

## iii. Table of contents

- A. Field equations and trace identity
- B. Starobinsky `R + α R²` model and Einstein-frame plateau

## iv. References

* Hans A. Buchdahl, *Non-Linear Lagrangians and Cosmological Theory*, *Monthly Notices of the Royal
  Astronomical Society* 150, pp. 1-8 (1970), Sec. 2. [ref: Buchdahl1970]
* Alexei A. Starobinsky, *A New Type of Isotropic Cosmological Models Without Singularity*, *Physics
  Letters B* 91, pp. 99-102 (1980). [ref: Starobinsky1980]
* Thomas P. Sotiriou and Valerio Faraoni, *f(R) Theories of Gravity*, *Reviews of Modern Physics*
  (2010), Sec. II-III (https://arxiv.org/pdf/0805.1726#page=3). [ref: SotiriouFaraoni2010]
-/

@[expose] public section

namespace GeneralRelativity

namespace Modified

namespace FRGravity

/-!

## A. Field equations and trace identity

Evaluating the variational derivative of `f(R)` produces `T.algebraicFieldEqn M R` plus covariant
second derivatives of `T.df`; taking the metric trace isolates the dynamical scalar mode.

-/

/-- A metric `f(R)` gravity theory specified by the scalar-curvature Lagrangian `f(R)` and its
first derivative `df(R) = f'(R)`. -/
structure FRTheory where
  /-- Scalar-curvature Lagrangian function `f(R)`. -/
  f : ℝ → ℝ
  /-- First derivative `f'(R)` entering the field equations. -/
  df : ℝ → ℝ
  /-- The stored derivative agrees with the derivative of `f` at every curvature. -/
  deriv_eq : ∀ R, HasDerivAt f (df R) R

/-- General Relativity with cosmological constant `Λ`, realized as `f(R) = R - 2 Λ`. -/
def FRTheory.generalRelativity (Λ : ℝ) : FRTheory where
  f S := S - 2 * Λ
  df _ := 1
  deriv_eq R := by
    simpa using (hasDerivAt_id R).sub_const (2 * Λ)

/-- Starobinsky quadratic gravity `f(R) = R + α R²`. -/
def FRTheory.starobinsky (α : ℝ) : FRTheory where
  f S := S + α * S ^ 2
  df S := 1 + 2 * α * S
  deriv_eq R := by
    have h := (hasDerivAt_id R).add ((hasDerivAt_pow 2 R).const_mul α)
    convert h using 1
    · ext S
      simp only [Pi.add_apply, id]
    · ring

/-- The algebraic metric-formalism `f(R)` field equation tensor
`f'(R) Ric_{ij} - (1/2) f(R) g_{ij}` evaluated on a spacetime metric and Riemann curvature tensor
(exact when `f'(R)` is constant so `-∇_i ∇_j f' + g_{ij} □f'` vanishes). -/
noncomputable def FRTheory.algebraicFieldEqn (T : FRTheory) {n : ℕ} (M : MetricTensor n)
    (R : RiemannTensor n) : Tensor2 n :=
  fun i j => T.df (ricciScalar M R) * ricci M R i j - (1 / 2) * T.f (ricciScalar M R) * M.g i j

/-- `f(R) = R - 2 Λ` reduces exactly to general relativity with cosmological constant `Λ`, whose
equations read `G + Λ g = 0`. -/
lemma linear_is_einstein {n : ℕ} (M : MetricTensor n) (R : RiemannTensor n) (Λ : ℝ) :
    (FRTheory.generalRelativity Λ).algebraicFieldEqn M R
      = fun i j => einstein M R i j + Λ * M.g i j := by
  funext i j
  simp only [FRTheory.algebraicFieldEqn, FRTheory.generalRelativity, einstein]
  ring

/-- Trace of the metric-formalism `f(R)` field equation tensor
`f'(R) Ric_{ij} - ½ f(R) g_{ij} + (g_{ij} □f' - ∇_i ∇_j f')` in `n` dimensions, yielding
`f'(R) R - (n/2) f(R) + (n - 1) □f'`. -/
lemma trace_algebraicFieldEqn (T : FRTheory) {n : ℕ} (M : MetricTensor n) (R : RiemannTensor n)
    (box : ℝ) (d2 : Tensor2 n) (hbox : metricTrace M d2 = box) :
    metricTrace M (fun i j => T.df (ricciScalar M R) * ricci M R i j
        - (1 / 2) * T.f (ricciScalar M R) * M.g i j + (M.g i j * box - d2 i j))
      = T.df (ricciScalar M R) * ricciScalar M R
        - (1 / 2) * T.f (ricciScalar M R) * (n : ℝ) + ((n : ℝ) - 1) * box := by
  have hcomm : (fun i j => M.g i j * box) = fun i j => box * M.g i j := by
    funext i j
    ring
  have h1 := metricTrace_add_fun M
    (fun i j => T.df (ricciScalar M R) * ricci M R i j
      - (1 / 2) * T.f (ricciScalar M R) * M.g i j)
    (fun i j => M.g i j * box - d2 i j)
  have h2 := metricTrace_sub_fun M
    (fun i j => T.df (ricciScalar M R) * ricci M R i j)
    (fun i j => (1 / 2) * T.f (ricciScalar M R) * M.g i j)
  have h3 := metricTrace_sub_fun M (fun i j => M.g i j * box) d2
  have h4 := metricTrace_smul_fun M (T.df (ricciScalar M R)) (ricci M R)
  have h5 := metricTrace_mul_g M box
  have h6 := metricTrace_mul_g M ((1 / 2) * T.f (ricciScalar M R))
  rw [h1, h2, h3, hcomm, h5, h6, h4, ← ricciScalar_eq_metricTrace, hbox]
  ring

/-- Four-dimensional trace of the `f(R)` field equation tensor:
`f'(R) R - 2 f(R) + 3 □f'`. -/
lemma trace_algebraicFieldEqn_four (T : FRTheory) (M : MetricTensor 4) (R : RiemannTensor 4)
    (box : ℝ) (d2 : Tensor2 4) (hbox : metricTrace M d2 = box) :
    metricTrace M (fun i j => T.df (ricciScalar M R) * ricci M R i j
        - (1 / 2) * T.f (ricciScalar M R) * M.g i j + (M.g i j * box - d2 i j))
      = T.df (ricciScalar M R) * ricciScalar M R - 2 * T.f (ricciScalar M R) + 3 * box := by
  rw [trace_algebraicFieldEqn T M R box d2 hbox]
  push_cast
  ring

/-!

## B. Starobinsky `R + α R²` model and Einstein-frame plateau

Legendre-transforming `FRTheory.starobinsky α` and rescaling to the Einstein frame produces a flat
exponential-approach slow-roll inflationary plateau `U(φ) → 1 / (8 α)`.

-/

/-- The Starobinsky Legendre potential `V(φ) = (φ - 1)² / (8 α)` associated with
`f(R) = R + α R²` and `φ = f'(R) = 1 + 2 α R`. -/
noncomputable def starobinskyPotential (α φ : ℝ) : ℝ := (φ - 1) ^ 2 / (8 * α)

/-- Inversion of `(FRTheory.starobinsky α).df R = φ`: `R = (φ - 1) / (2 α)`. -/
lemma starobinsky_scalar_inversion (α φ : ℝ) (hα : α ≠ 0) :
    (FRTheory.starobinsky α).df ((φ - 1) / (2 * α)) = φ := by
  have h2 : (2 : ℝ) * α ≠ 0 := mul_ne_zero (by norm_num) hα
  simp only [FRTheory.starobinsky]
  field_simp
  ring

/-- The Legendre transform `(φ R(φ) - f(R(φ))) / 2` for `FRTheory.starobinsky α` equals the
quadratic Starobinsky potential `(φ - 1)² / (8 α)`. -/
lemma starobinskyPotential_eq (α φ : ℝ) (hα : α ≠ 0) :
    (φ * ((φ - 1) / (2 * α)) - (FRTheory.starobinsky α).f ((φ - 1) / (2 * α))) / 2 =
      starobinskyPotential α φ := by
  have h2 : (2 : ℝ) * α ≠ 0 := mul_ne_zero (by norm_num) hα
  have h8 : (8 : ℝ) * α ≠ 0 := mul_ne_zero (by norm_num) hα
  simp only [FRTheory.starobinsky, starobinskyPotential]
  field_simp
  ring

/-- For `α ≠ 0`, `(FRTheory.starobinsky α).df` is non-constant, so `R + α R²` propagates an
extra scalar degree of freedom beyond general relativity. -/
lemma starobinsky_nonconstant_deriv (α : ℝ) (hα : α ≠ 0) :
    ∃ S : ℝ, (FRTheory.starobinsky α).df S ≠ 1 := by
  refine ⟨1 / (2 * α), ?_⟩
  have h : 2 * α * (1 / (2 * α)) = 1 := by
    have h2 : (2 : ℝ) * α ≠ 0 := mul_ne_zero (by norm_num) hα
    field_simp
  intro heq
  simp only [FRTheory.starobinsky] at heq
  rw [h] at heq
  norm_num at heq

/-- The Einstein-frame potential `U(φ) = V(φ) / φ²` under conformal rescaling `g̃ = φ g` in 4D,
preserving `√(-g) V(φ) = √(-g̃) U(φ)` when `V` is the normalized Jordan-frame potential
`(φ R - f) / 2`. -/
noncomputable def einsteinFramePotential (V : ℝ → ℝ) (φ : ℝ) : ℝ := V φ / φ ^ 2

/-- Einstein-frame Starobinsky potential: `U(φ) = (φ - 1)² / (8 α φ²)`. -/
lemma starobinsky_einsteinFrame (α φ : ℝ) (hα : α ≠ 0) (hφ : φ ≠ 0) :
    einsteinFramePotential (starobinskyPotential α) φ = (φ - 1) ^ 2 / (8 * α * φ ^ 2) := by
  have h8 : (8 : ℝ) * α ≠ 0 := mul_ne_zero (by norm_num) hα
  have hφ2 : φ ^ 2 ≠ 0 := pow_ne_zero 2 hφ
  simp only [einsteinFramePotential, starobinskyPotential]
  field_simp

/-- Plateau form of the Einstein-frame Starobinsky potential:
`U(φ) = (1 / (8 α)) (1 - 1 / φ)²`. -/
lemma starobinsky_einsteinFrame_form (α φ : ℝ) (hα : α ≠ 0) (hφ : φ ≠ 0) :
    einsteinFramePotential (starobinskyPotential α) φ = (1 / (8 * α)) * (1 - 1 / φ) ^ 2 := by
  rw [starobinsky_einsteinFrame α φ hα hφ]
  have h8 : (8 : ℝ) * α * φ ^ 2 ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) hα) (pow_ne_zero 2 hφ)
  field_simp

/-- The slow-roll plateau: as `φ → ∞`, the Einstein-frame potential approaches `1 / (8 α)`. -/
lemma starobinsky_plateau (α : ℝ) (hα : α ≠ 0) :
    Filter.Tendsto (fun φ : ℝ => einsteinFramePotential (starobinskyPotential α) φ) Filter.atTop
      (nhds (1 / (8 * α))) := by
  have hinv : Filter.Tendsto (fun φ : ℝ => 1 / φ) Filter.atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop Filter.tendsto_id
  have h1 : Filter.Tendsto (fun φ : ℝ => 1 - 1 / φ) Filter.atTop (nhds 1) := by
    simpa using tendsto_const_nhds.sub hinv
  have hsq : Filter.Tendsto (fun φ : ℝ => (1 - 1 / φ) ^ 2) Filter.atTop (nhds 1) := by
    simpa using h1.pow 2
  have hmul : Filter.Tendsto (fun φ : ℝ => (1 / (8 * α)) * (1 - 1 / φ) ^ 2)
      Filter.atTop (nhds ((1 / (8 * α)) * 1)) := tendsto_const_nhds.mul hsq
  have heq : (fun φ : ℝ => einsteinFramePotential (starobinskyPotential α) φ)
      =ᶠ[Filter.atTop] fun φ : ℝ => (1 / (8 * α)) * (1 - 1 / φ) ^ 2 := by
    filter_upwards [Filter.eventually_atTop.2 ⟨1, fun b hb => hb⟩] with φ hφ
    exact starobinsky_einsteinFrame_form α φ hα (by linarith)
  refine Filter.Tendsto.congr' heq.symm ?_
  simpa using hmul

end FRGravity

end Modified

end GeneralRelativity
