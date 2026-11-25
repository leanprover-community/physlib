/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

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

This module isolates the algebraic curvature equations from the fourth-order derivative terms
`-∇_i ∇_j f'(R) + g_{ij} □f'(R)` (which vanish whenever `f'` is constant, i.e., for constant-scalar
or General Relativity solutions) and formalises:

- the algebraic part `algebraicFieldEqn` of the `f(R)` field equation and its reduction to `G + Λ
  g` when `f(R) = R - 2 Λ` (`linear_is_einstein`);
- the `n`-dimensional trace identity `f'(S) S - (n/2) f(S) + (n - 1) □f' = 0`
  (`trace_algebraicFieldEqn`)
  and its four-dimensional `3 □f'` specialisation (`trace_algebraicFieldEqn_four`);
- Starobinsky's `R + α R²` Legendre potential `(φ - 1)² / (8 α)`, scalar mass `m² = 1 / (6 α)`,
  and the Einstein-frame plateau `U(φ) = (1 - 1/φ)² / (16 α) → 1 / (16 α)` as `φ → ∞`.

## ii. Key results

- `FRTheory` : `f(R)` gravity model specified by its Lagrangian function `f` and derivative
  `df`.
- `algebraicFieldEqn`, `linear_is_einstein` : algebraic `f(R)` equations and recovery of `G + Λ g`.
- `trace_algebraicFieldEqn`, `trace_algebraicFieldEqn_four` : trace equation showing the
  propagating scalar mode.
- `starobinskyPotential`, `starobinsky_scalar_inversion`, `potential_eq`,
  `starobinsky_nonconstant_deriv` : Starobinsky `R + α R²` potential and scalar degree of freedom.
- `einsteinFrameV`, `starobinsky_einsteinFrame_form`, `starobinsky_plateau` : Einstein-frame
  conformal potential and asymptotic slow-roll plateau.

## iii. Table of contents

- A. Field equations and trace identity
- B. Starobinsky `R + α R²` model and Einstein-frame plateau

## iv. References

* Hans A. Buchdahl, *Non-Linear Lagrangians and Cosmological Theory*, *Monthly Notices of the
  Royal Astronomical Society* (1970). [ref: Buchdahl1970]
* Alexei A. Starobinsky, *A New Type of Isotropic Cosmological Models Without Singularity*,
  *Physics Letters B* (1980). [ref: Starobinsky1980]
* Thomas P. Sotiriou and Valerio Faraoni, *f(R) Theories of Gravity*, *Reviews of Modern Physics*
  (2010) (https://arxiv.org/abs/0805.1726). [ref: SotiriouFaraoni2010]

-/

@[expose] public section

namespace GeneralRelativity

namespace Modified

namespace FRGravity

/-!

## A. Field equations and trace identity

-/

/-- A metric `f(R)` gravity theory specified by the scalar-curvature Lagrangian `f(R)` and its
first derivative `df(R) = f'(R)`. -/
structure FRTheory where
  /-- Scalar-curvature Lagrangian function `f(R)`. -/
  f : ℝ → ℝ
  /-- First derivative `f'(R)` entering the field equations. -/
  df : ℝ → ℝ

/-- The algebraic part `f'(S) Ric_{ij} - (1/2) f(S) g_{ij}` of the metric-formalism `f(R)`
field equations (exact when `f'` is constant so `-∇_i ∇_j f' + g_{ij} □f'` vanishes). -/
noncomputable def algebraicFieldEqn (f df : ℝ → ℝ) {n : ℕ} (M : MetricTensor n) (R :
  RiemannTensor n) :
    Tensor2 n :=
  fun i j => df (ricciScalar M R) * ricci M R i j - (1 / 2) * f (ricciScalar M R) * M.g i j

/-- `f(R) = R - 2 Λ` reduces exactly to general relativity with cosmological constant `Λ`,
`G + Λ g`. -/
lemma linear_is_einstein {n : ℕ} (M : MetricTensor n) (R : RiemannTensor n) (Λ : ℝ) :
    algebraicFieldEqn (fun S => S - 2 * Λ) (fun _ => 1) M R
      = fun i j => einstein M R i j + Λ * M.g i j := by
  funext i j
  simp only [algebraicFieldEqn, einstein]
  ring

/-- Trace of the metric-formalism `f(R)` field equation in `n` dimensions:
`f'(S) S - (n/2) f(S) + (n - 1) □f'`. -/
lemma trace_algebraicFieldEqn {n : ℕ} (M : MetricTensor n) (R : RiemannTensor n) (f df : ℝ → ℝ)
    (box : ℝ) (d2 : Tensor2 n) (hbox : metricTrace M d2 = box) :
    metricTrace M (fun i j => df (ricciScalar M R) * ricci M R i j
        - (1 / 2) * f (ricciScalar M R) * M.g i j + (M.g i j * box - d2 i j))
      = df (ricciScalar M R) * ricciScalar M R
        - (1 / 2) * f (ricciScalar M R) * (n : ℝ) + ((n : ℝ) - 1) * box := by
  have hcomm : (fun i j => M.g i j * box) = fun i j => box * M.g i j := by
    funext i j
    ring
  have h1 := metricTrace_add_fun M
    (fun i j => df (ricciScalar M R) * ricci M R i j - (1 / 2) * f (ricciScalar M R) * M.g i j)
    (fun i j => M.g i j * box - d2 i j)
  have h2 := metricTrace_sub_fun M
    (fun i j => df (ricciScalar M R) * ricci M R i j)
    (fun i j => (1 / 2) * f (ricciScalar M R) * M.g i j)
  have h3 := metricTrace_sub_fun M (fun i j => M.g i j * box) d2
  have h4 := metricTrace_smul M (df (ricciScalar M R)) (ricci M R)
  have h5 := metricTrace_mul_g M box
  have h6 := metricTrace_mul_g M ((1 / 2) * f (ricciScalar M R))
  rw [h1, h2, h3, hcomm, h5, h6, h4, ← ricciScalar_eq_metricTrace, hbox]
  ring

/-- In four dimensions, the trace equation becomes `f'(S) S - 2 f(S) + 3 □f' = 0`. -/
lemma trace_algebraicFieldEqn_four (M : MetricTensor 4) (R : RiemannTensor 4) (f df : ℝ → ℝ)
    (box : ℝ) (d2 : Tensor2 4) (hbox : metricTrace M d2 = box) :
    metricTrace M (fun i j => df (ricciScalar M R) * ricci M R i j
        - (1 / 2) * f (ricciScalar M R) * M.g i j + (M.g i j * box - d2 i j))
      = df (ricciScalar M R) * ricciScalar M R - 2 * f (ricciScalar M R) + 3 * box := by
  rw [trace_algebraicFieldEqn M R f df box d2 hbox]
  push_cast
  ring

/-!

## B. Starobinsky `R + α R²` model and Einstein-frame plateau

-/

/-- The Starobinsky Legendre potential `V(φ) = (φ - 1)² / (8 α)` associated with
`f(R) = R + α R²` and `φ = f'(R) = 1 + 2 α R`. -/
noncomputable def starobinskyPotential (α φ : ℝ) : ℝ := (φ - 1) ^ 2 / (8 * α)

/-- Inversion of `φ = 1 + 2 α R`: `R = (φ - 1) / (2 α)`. -/
lemma starobinsky_scalar_inversion (α φ : ℝ) (hα : α ≠ 0) :
    1 + 2 * α * ((φ - 1) / (2 * α)) = φ := by
  have h2 : (2 : ℝ) * α ≠ 0 := mul_ne_zero (by norm_num) hα
  field_simp
  ring

/-- The Legendre transform `(φ R(φ) - f(R(φ))) / 2` for `f(R) = R + α R²` equals the
quadratic Starobinsky potential `(φ - 1)² / (8 α)`. -/
lemma potential_eq (α φ : ℝ) (hα : α ≠ 0) :
    (φ * ((φ - 1) / (2 * α))
        - (((φ - 1) / (2 * α)) + α * ((φ - 1) / (2 * α)) ^ 2)) / 2 =
      starobinskyPotential α φ := by
  have h2 : (2 : ℝ) * α ≠ 0 := mul_ne_zero (by norm_num) hα
  have h8 : (8 : ℝ) * α ≠ 0 := mul_ne_zero (by norm_num) hα
  simp only [starobinskyPotential]
  field_simp
  ring

/-- For `α ≠ 0`, `f'(S) = 1 + 2 α S` is non-constant, so `R + α R²` propagates an extra scalar
degree of freedom beyond general relativity. -/
lemma starobinsky_nonconstant_deriv (α : ℝ) (hα : α ≠ 0) : ∃ S : ℝ, 1 + 2 * α * S ≠ 1 := by
  refine ⟨1 / (2 * α), ?_⟩
  have h : 2 * α * (1 / (2 * α)) = 1 := by
    have h2 : (2 : ℝ) * α ≠ 0 := mul_ne_zero (by norm_num) hα
    field_simp
  intro heq
  rw [h] at heq
  norm_num at heq

/-- The Einstein-frame potential `U(φ) = V(φ) / (2 φ²)` under conformal rescaling `g̃ = φ g`. -/
noncomputable def einsteinFrameV (V : ℝ → ℝ) (φ : ℝ) : ℝ := V φ / (2 * φ ^ 2)

/-- Einstein-frame Starobinsky potential: `U(φ) = (φ - 1)² / (16 α φ²)`. -/
lemma starobinsky_einsteinFrame (α φ : ℝ) (hα : α ≠ 0) (hφ : φ ≠ 0) :
    einsteinFrameV (starobinskyPotential α) φ = (φ - 1) ^ 2 / (16 * α * φ ^ 2) := by
  have h8 : (8 : ℝ) * α ≠ 0 := mul_ne_zero (by norm_num) hα
  have h2 : (2 : ℝ) * φ ^ 2 ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero 2 hφ)
  simp only [einsteinFrameV, starobinskyPotential]
  field_simp
  ring

/-- Plateau form of the Einstein-frame Starobinsky potential:
`U(φ) = (1 / (16 α)) (1 - 1 / φ)²`. -/
lemma starobinsky_einsteinFrame_form (α φ : ℝ) (hα : α ≠ 0) (hφ : φ ≠ 0) :
    einsteinFrameV (starobinskyPotential α) φ = (1 / (16 * α)) * (1 - 1 / φ) ^ 2 := by
  rw [starobinsky_einsteinFrame α φ hα hφ]
  have h16 : (16 : ℝ) * α * φ ^ 2 ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) hα) (pow_ne_zero 2 hφ)
  field_simp

/-- The slow-roll plateau: as `φ → ∞`, the Einstein-frame potential approaches `1 / (16 α)`. -/
lemma starobinsky_plateau (α : ℝ) (hα : α ≠ 0) :
    Filter.Tendsto (fun φ : ℝ => einsteinFrameV (starobinskyPotential α) φ) Filter.atTop
      (nhds (1 / (16 * α))) := by
  have hinv : Filter.Tendsto (fun φ : ℝ => 1 / φ) Filter.atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop Filter.tendsto_id
  have h1 : Filter.Tendsto (fun φ : ℝ => 1 - 1 / φ) Filter.atTop (nhds 1) := by
    simpa using tendsto_const_nhds.sub hinv
  have hsq : Filter.Tendsto (fun φ : ℝ => (1 - 1 / φ) ^ 2) Filter.atTop (nhds 1) := by
    simpa using h1.pow 2
  have hmul : Filter.Tendsto (fun φ : ℝ => (1 / (16 * α)) * (1 - 1 / φ) ^ 2)
      Filter.atTop (nhds ((1 / (16 * α)) * 1)) := tendsto_const_nhds.mul hsq
  have heq : (fun φ : ℝ => einsteinFrameV (starobinskyPotential α) φ)
      =ᶠ[Filter.atTop] fun φ : ℝ => (1 / (16 * α)) * (1 - 1 / φ) ^ 2 := by
    filter_upwards [Filter.eventually_atTop.2 ⟨1, fun b hb => hb⟩] with φ hφ
    exact starobinsky_einsteinFrame_form α φ hα (by linarith)
  refine Filter.Tendsto.congr' heq.symm ?_
  simpa using hmul

/-- The algebraic metric-formalism `f(R)` field equation tensor evaluated on the metric tensor `M`
and Riemann curvature tensor `R`. -/
noncomputable def FRTheory.algebraicFieldEqn (T : FRTheory) {n : ℕ} (M : MetricTensor n)
    (R : RiemannTensor n) : Tensor2 n :=
  FRGravity.algebraicFieldEqn T.f T.df M R

end FRGravity

end Modified

end GeneralRelativity
