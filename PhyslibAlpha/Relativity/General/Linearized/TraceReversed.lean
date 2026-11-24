/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import PhyslibAlpha.Relativity.Metrics.CoordinateMetric
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Ring

/-!

# Trace-reversed metric perturbations and wave operator

Trace reversal `h̄_{ij} = h_{ij} - ½ η_{ij} h`, the Minkowski d'Alembertian `□_η`, and
coordinate partial-derivative calculus helpers for linearized gravity.

## i. Overview

Around four-dimensional Minkowski spacetime `eta4`, a weak-field metric perturbation `h` has
Minkowski trace `hTrace h = η^{ab} h_{ab}` and trace-reversed perturbation
`traceReversed h = h - ½ η hTrace h`. Trace reversal is an involution (`traceReversed_involutive`)
that flips the sign of the trace (`traceReversed_trace`) and preserves symmetry. This module also
defines the flat-space wave operator `boxEta` and establishes coordinate partial-derivative
linearity and Schwarz commutativity `∂_μ ∂_ν f = ∂_ν ∂_μ f` for `C²` scalar fields.

## ii. Key results

- `hTrace`, `traceReversed`, `traceReversed_trace`, `traceReversed_involutive`,
  `traceReversed_symm` : Minkowski trace and trace-reversal involution.
- `boxEta` : Minkowski d'Alembertian wave operator `□_η`.
- `pd_congr_nhds`, `pd_eq_fderiv`, `pd_comm`, `pd_add`, `pd_sub`, `pd_const_mul`, `pd_sum` :
  coordinate partial-derivative calculus helpers.

## iii. Table of contents

- A. Trace reversal and wave operator
- B. Partial derivative calculus helpers

## iv. References

* R. M. Wald, *General Relativity* (1984). [ref: wald_1984_general_relativity]
* C. W. Misner, K. S. Thorne, and J. A. Wheeler, *Gravitation* (1973). [ref: mtw_1973_gravitation]

-/

@[expose] public section

namespace GeneralRelativity

namespace Linearized

open Pipeline

/-!

## A. Trace reversal and wave operator

-/

/-- Minkowski trace `h = η^{ij} h_{ij}` of a symmetric `(0,2)` metric perturbation. -/
noncomputable def hTrace (h : Tensor2 4) : ℝ := ∑ a : Fin 4, eta4 a a * h a a

/-- Trace-reversed perturbation `h̄_{ij} = h_{ij} - (1 / 2) η_{ij} h`. -/
noncomputable def traceReversed (h : Tensor2 4) : Tensor2 4 :=
  fun i j => h i j - (1 / 2) * eta4 i j * hTrace h

/-- Trace of the trace-reversed perturbation is `-hTrace h`. -/
lemma traceReversed_trace (h : Tensor2 4) : hTrace (traceReversed h) = -hTrace h := by
  simp [hTrace, traceReversed, Fin.sum_univ_four]
  ring

/-- Trace reversal is an involution: `(h̄)̄ = h`. -/
lemma traceReversed_involutive (h : Tensor2 4) : traceReversed (traceReversed h) = h := by
  ext i j
  simp only [traceReversed, traceReversed_trace]
  ring

/-- Symmetry is preserved by trace reversal. -/
lemma traceReversed_symm {h : Tensor2 4} (hs : IsSymm h) : IsSymm (traceReversed h) := by
  intro i j
  simp only [traceReversed, hs i j, eta4_symm i j]

/-- Minkowski d'Alembertian (wave operator) `□f = η^{μν} ∂_μ ∂_ν f = -∂_t² f + ∇² f`. -/
noncomputable def boxEta (f : (Fin 4 → ℝ) → ℝ) (x : Fin 4 → ℝ) : ℝ :=
  ∑ μ : Fin 4, eta4 μ μ * pd μ (pd μ f) x

/-!

## B. Partial derivative calculus helpers

-/

/-- Agreement of partial derivatives for locally equal functions on a neighborhood of `x`. -/
lemma pd_congr_nhds (μ : Fin 4) {f g : (Fin 4 → ℝ) → ℝ} (x : Fin 4 → ℝ)
    (hfg : f =ᶠ[nhds x] g) : pd μ f x = pd μ g x := by
  have hcont : Continuous (fun s : ℝ => Function.update x μ s) := by
    rw [continuous_pi_iff]
    intro k
    by_cases hk : k = μ
    · subst hk; simp only [Function.update_self]; exact continuous_id
    · simp only [Function.update, hk, ↓reduceDIte]; exact continuous_const
  have htend : Filter.Tendsto (fun s : ℝ => Function.update x μ s) (nhds (x μ)) (nhds x) := by
    convert hcont.continuousAt.tendsto using 1
    simp [Function.update_eq_self]
  exact (hfg.comp_tendsto htend).deriv_eq

/-- Partial derivative along axis `μ` equals directional Fréchet derivative along
`Pi.single μ 1`. -/
lemma pd_eq_fderiv {f : (Fin 4 → ℝ) → ℝ} {x : Fin 4 → ℝ} {μ : Fin 4}
    (hf : DifferentiableAt ℝ f x) :
    pd μ f x = fderiv ℝ f x (Pi.single μ 1) := by
  have hupd : (fun s : ℝ => Function.update x μ s)
      = fun s => x + (s - x μ) • (Pi.single μ 1 : Fin 4 → ℝ) := by
    ext s k
    by_cases hk : k = μ <;> simp [Function.update, hk]
  have hd : HasDerivAt (fun s : ℝ => Function.update x μ s) (Pi.single μ (1 : ℝ)) (x μ) := by
    rw [hupd]
    have h1 : HasDerivAt (fun s : ℝ => s - x μ) 1 (x μ) := by
      simpa using (hasDerivAt_id (x μ)).sub_const (x μ)
    simpa using (h1.smul_const (Pi.single μ (1 : ℝ))).const_add x
  rw [pd]
  have hf' : HasFDerivAt f (fderiv ℝ f x) (Function.update x μ (x μ)) := by
    simpa [Function.update_eq_self] using hf.hasFDerivAt
  exact (hf'.comp_hasDerivAt (x μ) hd).deriv

/-- Schwarz symmetry of mixed second coordinate partial derivatives for `ContDiffAt ℝ 2`
fields. -/
lemma pd_comm {f : (Fin 4 → ℝ) → ℝ} {x : Fin 4 → ℝ} (μ ν : Fin 4)
    (hf : ContDiffAt ℝ 2 f x) :
    pd μ (pd ν f) x = pd ν (pd μ f) x := by
  have hf_nhds : ∀ᶠ y in nhds x, ContDiffAt ℝ 2 f y := hf.eventually (by simp)
  have hcongr1 : pd ν f =ᶠ[nhds x] fun y => fderiv ℝ f y (Pi.single ν 1) :=
    hf_nhds.mono fun y hy => pd_eq_fderiv (hy.differentiableAt (by norm_num))
  have hcongr2 : pd μ f =ᶠ[nhds x] fun y => fderiv ℝ f y (Pi.single μ 1) :=
    hf_nhds.mono fun y hy => pd_eq_fderiv (hy.differentiableAt (by norm_num))
  have hdf' : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hdiff1 : DifferentiableAt ℝ (fun y => fderiv ℝ f y (Pi.single ν 1)) x :=
    hdf'.clm_apply (differentiableAt_const _)
  have hdiff2 : DifferentiableAt ℝ (fun y => fderiv ℝ f y (Pi.single μ 1)) x :=
    hdf'.clm_apply (differentiableAt_const _)
  rw [pd_congr_nhds μ x hcongr1, pd_congr_nhds ν x hcongr2,
    pd_eq_fderiv hdiff1, pd_eq_fderiv hdiff2]
  have hcl1 : fderiv ℝ (fun y => fderiv ℝ f y (Pi.single ν 1)) x (Pi.single μ 1)
      = fderiv ℝ (fderiv ℝ f) x (Pi.single μ 1) (Pi.single ν 1) := by
    rw [(hdf'.hasFDerivAt.clm_apply (hasFDerivAt_const _ x)).fderiv]
    simp
  have hcl2 : fderiv ℝ (fun y => fderiv ℝ f y (Pi.single μ 1)) x (Pi.single ν 1)
      = fderiv ℝ (fderiv ℝ f) x (Pi.single ν 1) (Pi.single μ 1) := by
    rw [(hdf'.hasFDerivAt.clm_apply (hasFDerivAt_const _ x)).fderiv]
    simp
  rw [hcl1, hcl2]
  exact (hf.isSymmSndFDerivAt (by norm_num)).eq _ _

/-- Linearity of `pd` under pointwise addition of differentiable coordinate slices. -/
lemma pd_add (μ : Fin 4) {f g : (Fin 4 → ℝ) → ℝ} (x : Fin 4 → ℝ)
    (hf : DifferentiableAt ℝ (fun s => f (Function.update x μ s)) (x μ))
    (hg : DifferentiableAt ℝ (fun s => g (Function.update x μ s)) (x μ)) :
    pd μ (fun y => f y + g y) x = pd μ f x + pd μ g x :=
  deriv_add hf hg

/-- Linearity of `pd` under pointwise subtraction of differentiable coordinate slices. -/
lemma pd_sub (μ : Fin 4) {f g : (Fin 4 → ℝ) → ℝ} (x : Fin 4 → ℝ)
    (hf : DifferentiableAt ℝ (fun s => f (Function.update x μ s)) (x μ))
    (hg : DifferentiableAt ℝ (fun s => g (Function.update x μ s)) (x μ)) :
    pd μ (fun y => f y - g y) x = pd μ f x - pd μ g x :=
  deriv_sub hf hg

/-- Linearity of `pd` under constant scalar multiplication. -/
lemma pd_const_mul (μ : Fin 4) (c : ℝ) {f : (Fin 4 → ℝ) → ℝ} (x : Fin 4 → ℝ) :
    pd μ (fun y => c * f y) x = c * pd μ f x := by
  simp only [pd]
  exact deriv_const_mul_field c

/-- Linearity of `pd` over finite `Fin 4` sums of differentiable slices. -/
lemma pd_sum (μ : Fin 4) (F : Fin 4 → (Fin 4 → ℝ) → ℝ) (x : Fin 4 → ℝ)
    (hF : ∀ k, DifferentiableAt ℝ (fun s => F k (Function.update x μ s)) (x μ)) :
    pd μ (fun y => ∑ k : Fin 4, F k y) x = ∑ k : Fin 4, pd μ (F k) x := by
  have hs : (fun s => ∑ k : Fin 4, F k (Function.update x μ s))
      = ∑ k : Fin 4, fun s => F k (Function.update x μ s) := by
    funext s; simp only [Finset.sum_apply]
  simp only [pd, hs]
  exact deriv_sum fun k _ => hF k

/-- A `C³` scalar field has `C²` coordinate partial derivatives. -/
lemma contDiffAt_pd {f : (Fin 4 → ℝ) → ℝ} {x : Fin 4 → ℝ} (μ : Fin 4)
    (hf : ContDiffAt ℝ 3 f x) : ContDiffAt ℝ 2 (pd μ f) x := by
  have hf_nhds : ∀ᶠ y in nhds x, ContDiffAt ℝ 2 f y :=
    (hf.of_le (by norm_num)).eventually (by simp)
  have hcongr : pd μ f =ᶠ[nhds x] fun y => fderiv ℝ f y (Pi.single μ 1) :=
    hf_nhds.mono fun y hy => pd_eq_fderiv (hy.differentiableAt (by norm_num))
  have hdf' : ContDiffAt ℝ 2 (fderiv ℝ f) x := hf.fderiv_right (m := 2) (by norm_num)
  have hclm : ContDiffAt ℝ 2 (fun y => fderiv ℝ f y (Pi.single μ 1)) x :=
    hdf'.clm_apply contDiffAt_const
  exact hclm.congr_of_eventuallyEq hcongr

/-- A `C²` scalar field has differentiable coordinate partial derivatives. -/
lemma pd_differentiableAt {f : (Fin 4 → ℝ) → ℝ} {x : Fin 4 → ℝ} (μ : Fin 4)
    (hf : ContDiffAt ℝ 2 f x) :
    DifferentiableAt ℝ (fun y => pd μ f y) x := by
  have hf_nhds : ∀ᶠ y in nhds x, ContDiffAt ℝ 2 f y := hf.eventually (by simp)
  have hcongr : pd μ f =ᶠ[nhds x] fun y => fderiv ℝ f y (Pi.single μ 1) :=
    hf_nhds.mono fun y hy => pd_eq_fderiv (hy.differentiableAt (by norm_num))
  have hdf' : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  exact (hdf'.clm_apply (differentiableAt_const _)).congr_of_eventuallyEq hcongr

/-- A differentiable field on `ℝ⁴` has differentiable coordinate slices. -/
lemma slice_differentiableAt {f : (Fin 4 → ℝ) → ℝ} {x : Fin 4 → ℝ} (μ : Fin 4)
    (hf : DifferentiableAt ℝ f x) :
    DifferentiableAt ℝ (fun s => f (Function.update x μ s)) (x μ) := by
  have hupd : (fun s : ℝ => Function.update x μ s)
      = fun s => x + (s - x μ) • (Pi.single μ 1 : Fin 4 → ℝ) := by
    ext s k; by_cases hk : k = μ <;> simp [Function.update, hk]
  have hd : HasDerivAt (fun s : ℝ => Function.update x μ s) (Pi.single μ (1 : ℝ)) (x μ) := by
    rw [hupd]
    simpa using (((hasDerivAt_id (x μ)).sub_const (x μ)).smul_const
      (Pi.single μ (1 : ℝ))).const_add x
  have hf' : HasFDerivAt f (fderiv ℝ f x) (Function.update x μ (x μ)) := by
    simpa [Function.update_eq_self] using hf.hasFDerivAt
  exact (hf'.comp_hasDerivAt (x μ) hd).differentiableAt

/-- A `C²` metric perturbation has a `C²` trace-reversed perturbation. -/
lemma contDiffAt_traceReversed {h : (Fin 4 → ℝ) → Tensor2 4} {x : Fin 4 → ℝ}
    (hh : ∀ a b, ContDiffAt ℝ 2 (fun z => h z a b) x) (i j : Fin 4) :
    ContDiffAt ℝ 2 (fun y => traceReversed (h y) i j) x := by
  simp only [traceReversed, hTrace, Fin.sum_univ_four]
  have h0 : ContDiffAt ℝ 2 (fun y => eta4 0 0 * h y 0 0) x :=
    (contDiffAt_const (c := eta4 0 0)).mul (hh 0 0)
  have h1 : ContDiffAt ℝ 2 (fun y => eta4 1 1 * h y 1 1) x :=
    (contDiffAt_const (c := eta4 1 1)).mul (hh 1 1)
  have h2 : ContDiffAt ℝ 2 (fun y => eta4 2 2 * h y 2 2) x :=
    (contDiffAt_const (c := eta4 2 2)).mul (hh 2 2)
  have h3 : ContDiffAt ℝ 2 (fun y => eta4 3 3 * h y 3 3) x :=
    (contDiffAt_const (c := eta4 3 3)).mul (hh 3 3)
  exact (hh i j).sub ((contDiffAt_const (c := (1 / 2 : ℝ) * eta4 i j)).mul
    (((h0.add h1).add h2).add h3))

/-- A `C²` metric perturbation has a `C²` Minkowski trace. -/
lemma contDiffAt_hTrace {h : (Fin 4 → ℝ) → Tensor2 4} {x : Fin 4 → ℝ}
    (hh : ∀ a b, ContDiffAt ℝ 2 (fun z => h z a b) x) :
    ContDiffAt ℝ 2 (fun y => hTrace (h y)) x := by
  simp only [hTrace, Fin.sum_univ_four]
  have h0 : ContDiffAt ℝ 2 (fun y => eta4 0 0 * h y 0 0) x :=
    (contDiffAt_const (c := eta4 0 0)).mul (hh 0 0)
  have h1 : ContDiffAt ℝ 2 (fun y => eta4 1 1 * h y 1 1) x :=
    (contDiffAt_const (c := eta4 1 1)).mul (hh 1 1)
  have h2 : ContDiffAt ℝ 2 (fun y => eta4 2 2 * h y 2 2) x :=
    (contDiffAt_const (c := eta4 2 2)).mul (hh 2 2)
  have h3 : ContDiffAt ℝ 2 (fun y => eta4 3 3 * h y 3 3) x :=
    (contDiffAt_const (c := eta4 3 3)).mul (hh 3 3)
  exact ((h0.add h1).add h2).add h3

end Linearized

end GeneralRelativity
