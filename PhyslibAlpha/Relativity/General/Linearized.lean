/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import PhyslibAlpha.Relativity.General.Minkowski
public import PhyslibAlpha.Relativity.General.Pipeline
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!

# Linearized general relativity and gravitational waves

Weak-field perturbations `g = η + h` around Minkowski spacetime: trace-reversed perturbation,
linearized Riemann/Ricci/Einstein tensors, diffeomorphism gauge invariance, Lorenz gauge wave
equation `□h̄ = 0`, transverse-traceless `+`/`×` gravitational waves, and the Newtonian Poisson
limit.

## i. Overview

This module formalizes linearized gravity around four-dimensional Minkowski spacetime `eta4` with
`(-, +, +, +)` signature. After establishing coordinate partial-derivative linearity and Schwarz
commutativity `∂_μ ∂_ν f = ∂_ν ∂_μ f` for `C²` fields, it defines the trace `hTrace`, the
trace-reversed perturbation `traceReversed`, the linearized Christoffel, Riemann, Ricci, scalar, and
Einstein tensors, and proves: (1) invariance of the linearized Riemann, Ricci, and Einstein tensors
under infinitesimal diffeomorphisms `h' = h + ∂_i ξ_j + ∂_j ξ_i`; (2) reduction of `linEinstein`
to `-(1/2) □ h̄` in Lorenz gauge; (3) exact vacuum propagation of transverse-traceless (`+` and `×`)
plane gravitational waves; and (4) the weak-field Newtonian Poisson equation `∇² Φ = 4 π ρ`.

## ii. Key results

- `pd_comm` : Schwarz symmetry `∂_μ ∂_ν f = ∂_ν ∂_μ f` for `C²` scalar fields.
- `hTrace`, `traceReversed`, `traceReversed_involutive` : trace reversal
  `h̄_{ij} = h_{ij} - ½ η_{ij} h`.
- `linRiemann`, `linRicci`, `linEinstein`, `boxEta` : linearized curvature and wave operators.
- `linRiemann_gauge_invariant`, `linEinstein_gauge_invariant` : linearized diffeomorphism
  invariance.
- `linEinstein_lorenz_gauge` : Lorenz-gauge wave equation `linEinstein = -(1/2) □h̄`.
- `ttWave`, `ttWave_linEinstein_zero` : transverse-traceless gravitational waves satisfy
  `G^{lin} = 0`.
- `newtonianPerturb`, `newtonianPerturb_poisson_iff` : Newtonian Poisson limit `∇² Φ = 4 π ρ`.

## iii. Table of contents

- A. Partial derivative calculus helpers
- B. Trace reversal and linearized curvature
- C. Linearized diffeomorphism gauge invariance
- D. Lorenz gauge and gravitational wave propagation
- E. Transverse-traceless modes and Newtonian limit

## iv. References

* None.

-/

@[expose] public section

namespace GeneralRelativity

namespace Linearized

open Pipeline

/-!

## A. Partial derivative calculus helpers

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
      = fun s => x + (s - x μ) • Pi.single μ (1 : ℝ) := by
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

private lemma contDiffAt_pd {f : (Fin 4 → ℝ) → ℝ} {x : Fin 4 → ℝ} (μ : Fin 4)
    (hf : ContDiffAt ℝ 3 f x) : ContDiffAt ℝ 2 (pd μ f) x := by
  have hf_nhds : ∀ᶠ y in nhds x, ContDiffAt ℝ 2 f y :=
    (hf.of_le (by norm_num)).eventually (by simp)
  have hcongr : pd μ f =ᶠ[nhds x] fun y => fderiv ℝ f y (Pi.single μ 1) :=
    hf_nhds.mono fun y hy => pd_eq_fderiv (hy.differentiableAt (by norm_num))
  have hdf' : ContDiffAt ℝ 2 (fderiv ℝ f) x := hf.fderiv_right (m := 2) (by norm_num)
  have hclm : ContDiffAt ℝ 2 (fun y => fderiv ℝ f y (Pi.single μ 1)) x :=
    hdf'.clm_apply contDiffAt_const
  exact hclm.congr_of_eventuallyEq hcongr

private lemma pd_differentiableAt {f : (Fin 4 → ℝ) → ℝ} {x : Fin 4 → ℝ} (μ : Fin 4)
    (hf : ContDiffAt ℝ 2 f x) :
    DifferentiableAt ℝ (fun y => pd μ f y) x := by
  have hf_nhds : ∀ᶠ y in nhds x, ContDiffAt ℝ 2 f y := hf.eventually (by simp)
  have hcongr : pd μ f =ᶠ[nhds x] fun y => fderiv ℝ f y (Pi.single μ 1) :=
    hf_nhds.mono fun y hy => pd_eq_fderiv (hy.differentiableAt (by norm_num))
  have hdf' : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  exact (hdf'.clm_apply (differentiableAt_const _)).congr_of_eventuallyEq hcongr

private lemma slice_differentiableAt {f : (Fin 4 → ℝ) → ℝ} {x : Fin 4 → ℝ} (μ : Fin 4)
    (hf : DifferentiableAt ℝ f x) :
    DifferentiableAt ℝ (fun s => f (Function.update x μ s)) (x μ) := by
  have hupd : (fun s : ℝ => Function.update x μ s)
      = fun s => x + (s - x μ) • Pi.single μ (1 : ℝ) := by
    ext s k; by_cases hk : k = μ <;> simp [Function.update, hk]
  have hd : HasDerivAt (fun s : ℝ => Function.update x μ s) (Pi.single μ (1 : ℝ)) (x μ) := by
    rw [hupd]
    simpa using (((hasDerivAt_id (x μ)).sub_const (x μ)).smul_const
      (Pi.single μ (1 : ℝ))).const_add x
  have hf' : HasFDerivAt f (fderiv ℝ f x) (Function.update x μ (x μ)) := by
    simpa [Function.update_eq_self] using hf.hasFDerivAt
  exact (hf'.comp_hasDerivAt (x μ) hd).differentiableAt

/-!

## B. Trace reversal and linearized curvature

-/

/-- Minkowski trace `h = η^{ij} h_{ij}` of a symmetric `(0,2)` metric perturbation. -/
noncomputable def hTrace (h : Tensor2 4) : ℝ := ∑ a : Fin 4, eta4 a a * h a a

/-- Trace-reversed perturbation `h̄_{ij} = h_{ij} - (1 / 2) η_{ij} h`. -/
noncomputable def traceReversed (h : Tensor2 4) : Tensor2 4 :=
  fun i j => h i j - (1 / 2) * eta4 i j * hTrace h

/-- Trace of the trace-reversed perturbation is `-hTrace h`. -/
lemma traceReversed_trace (h : Tensor2 4) : hTrace (traceReversed h) = -hTrace h := by
  simp [hTrace, traceReversed, Fin.sum_univ_four, eta4]
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

/-- Linearized Christoffel symbols `Γ^k_{ij} = ½ η^{km} (∂_j h_{mi} + ∂_i h_{mj} - ∂_m h_{ij})`. -/
noncomputable def linChristoffel (h : (Fin 4 → ℝ) → Tensor2 4) (x : Fin 4 → ℝ)
    (k i j : Fin 4) : ℝ :=
  (1 / 2) * eta4 k k
    * (pd j (fun y => h y k i) x + pd i (fun y => h y k j) x - pd k (fun y => h y i j) x)

/-- Lower-index symmetry of linearized Christoffel symbols when `h` is symmetric. -/
lemma linChristoffel_symm (h : (Fin 4 → ℝ) → Tensor2 4) (x : Fin 4 → ℝ)
    (hs : ∀ y i j, h y i j = h y j i) (k i j : Fin 4) :
    linChristoffel h x k i j = linChristoffel h x k j i := by
  have hij : (fun y => h y i j) = fun y => h y j i := funext fun y => hs y i j
  simp only [linChristoffel, hij]
  ring

/-- Linearized Riemann curvature tensor `R^r_{s m n} = ∂_m Γ^r_{n s} - ∂_n Γ^r_{m s}`. -/
noncomputable def linRiemann (h : (Fin 4 → ℝ) → Tensor2 4) (x : Fin 4 → ℝ)
    (r s m n : Fin 4) : ℝ :=
  pd m (fun y => linChristoffel h y r n s) x - pd n (fun y => linChristoffel h y r m s) x

/-- Antisymmetry of `linRiemann` in its last two indices. -/
lemma linRiemann_antisymm (h : (Fin 4 → ℝ) → Tensor2 4) (x : Fin 4 → ℝ) (r s m n : Fin 4) :
    linRiemann h x r s m n = -linRiemann h x r s n m := by
  simp only [linRiemann]
  ring

/-- Linearized Ricci tensor `R^{(1)}_{ij} = ∑ r, R^r_{i r j}`. -/
noncomputable def linRicci (h : (Fin 4 → ℝ) → Tensor2 4) (x : Fin 4 → ℝ) (i j : Fin 4) : ℝ :=
  ∑ r : Fin 4, linRiemann h x r i r j

/-- Linearized Ricci scalar `S^{(1)} = η^{ij} R^{(1)}_{ij}`. -/
noncomputable def linScalar (h : (Fin 4 → ℝ) → Tensor2 4) (x : Fin 4 → ℝ) : ℝ :=
  ∑ i : Fin 4, eta4 i i * linRicci h x i i

/-- Linearized Einstein tensor `G^{(1)}_{ij} = R^{(1)}_{ij} - ½ η_{ij} S^{(1)}`. -/
noncomputable def linEinstein (h : (Fin 4 → ℝ) → Tensor2 4) (x : Fin 4 → ℝ)
    (i j : Fin 4) : ℝ :=
  linRicci h x i j - (1 / 2) * eta4 i j * linScalar h x

/-!

## C. Linearized diffeomorphism gauge invariance

-/

/-- Infinitesimal coordinate gauge transformation `h'_{ij} = h_{ij} + ∂_i ξ_j + ∂_j ξ_i`. -/
noncomputable def gaugeTransform (h : (Fin 4 → ℝ) → Tensor2 4)
    (ξ : (Fin 4 → ℝ) → (Fin 4 → ℝ)) (x : Fin 4 → ℝ) : Tensor2 4 :=
  fun i j => h x i j + pd i (fun y => ξ y j) x + pd j (fun y => ξ y i) x

/-- Pure-gauge metric perturbation `δh_{ij} = ∂_i ξ_j + ∂_j ξ_i`. -/
noncomputable def pureGauge (ξ : (Fin 4 → ℝ) → (Fin 4 → ℝ)) (x : Fin 4 → ℝ) : Tensor2 4 :=
  fun i j => pd i (fun y => ξ y j) x + pd j (fun y => ξ y i) x

private lemma linChristoffel_pureGauge (ξ : (Fin 4 → ℝ) → (Fin 4 → ℝ)) (x : Fin 4 → ℝ)
    (hξ : ∀ a, ContDiffAt ℝ 2 (fun z => ξ z a) x) (k i j : Fin 4) :
    linChristoffel (pureGauge ξ) x k i j
      = eta4 k k * pd j (pd i fun z => ξ z k) x := by
  have d_ki : DifferentiableAt ℝ (pd k fun z => ξ z i) x := pd_differentiableAt k (hξ i)
  have d_ik : DifferentiableAt ℝ (pd i fun z => ξ z k) x := pd_differentiableAt i (hξ k)
  have d_kj : DifferentiableAt ℝ (pd k fun z => ξ z j) x := pd_differentiableAt k (hξ j)
  have d_jk : DifferentiableAt ℝ (pd j fun z => ξ z k) x := pd_differentiableAt j (hξ k)
  have d_ij : DifferentiableAt ℝ (pd i fun z => ξ z j) x := pd_differentiableAt i (hξ j)
  have d_ji : DifferentiableAt ℝ (pd j fun z => ξ z i) x := pd_differentiableAt j (hξ i)
  simp only [linChristoffel, pureGauge]
  rw [pd_add j x (slice_differentiableAt j d_ki) (slice_differentiableAt j d_ik),
    pd_add i x (slice_differentiableAt i d_kj) (slice_differentiableAt i d_jk),
    pd_add k x (slice_differentiableAt k d_ij) (slice_differentiableAt k d_ji),
    pd_comm k i (hξ j), pd_comm k j (hξ i), pd_comm i j (hξ k)]
  ring

/-- Additivity of `linRiemann` for `C²` perturbations. -/
lemma linRiemann_add (h1 h2 : (Fin 4 → ℝ) → Tensor2 4) (x : Fin 4 → ℝ)
    (h1c : ∀ a b, ContDiffAt ℝ 2 (fun z => h1 z a b) x)
    (h2c : ∀ a b, ContDiffAt ℝ 2 (fun z => h2 z a b) x)
    (r s m n : Fin 4) :
    linRiemann (fun y a b => h1 y a b + h2 y a b) x r s m n
      = linRiemann h1 x r s m n + linRiemann h2 x r s m n := by
  have nh1 : ∀ᶠ y in nhds x, ∀ a b, ContDiffAt ℝ 2 (fun z => h1 z a b) y := by
    rw [Filter.eventually_all]; intro a; rw [Filter.eventually_all]; intro b
    exact (h1c a b).eventually (by simp)
  have nh2 : ∀ᶠ y in nhds x, ∀ a b, ContDiffAt ℝ 2 (fun z => h2 z a b) y := by
    rw [Filter.eventually_all]; intro a; rw [Filter.eventually_all]; intro b
    exact (h2c a b).eventually (by simp)
  have hcongr : ∀ k i j,
      (fun y => linChristoffel (fun z a b => h1 z a b + h2 z a b) y k i j) =ᶠ[nhds x]
        fun y => linChristoffel h1 y k i j + linChristoffel h2 y k i j := by
    intro k i j
    filter_upwards [nh1, nh2] with y hy1 hy2
    have d1 : ∀ a b, DifferentiableAt ℝ (fun z => h1 z a b) y :=
      fun a b => (hy1 a b).differentiableAt (by norm_num)
    have d2 : ∀ a b, DifferentiableAt ℝ (fun z => h2 z a b) y :=
      fun a b => (hy2 a b).differentiableAt (by norm_num)
    simp only [linChristoffel]
    rw [pd_add j y (slice_differentiableAt j (d1 k i)) (slice_differentiableAt j (d2 k i)),
      pd_add i y (slice_differentiableAt i (d1 k j)) (slice_differentiableAt i (d2 k j)),
      pd_add k y (slice_differentiableAt k (d1 i j)) (slice_differentiableAt k (d2 i j))]
    ring
  have hd_lin : ∀ h' : (Fin 4 → ℝ) → Tensor2 4, (∀ a b, ContDiffAt ℝ 2 (fun z => h' z a b) x) →
      ∀ k i j, DifferentiableAt ℝ (fun y => linChristoffel h' y k i j) x := by
    intro h' hh' k i j
    simp only [linChristoffel]
    exact (((pd_differentiableAt j (hh' k i)).add (pd_differentiableAt i (hh' k j))).sub
      (pd_differentiableAt k (hh' i j))).const_mul _
  simp only [linRiemann]
  rw [pd_congr_nhds m x (hcongr r n s),
    pd_congr_nhds n x (hcongr r m s),
    pd_add m x (slice_differentiableAt m (hd_lin h1 h1c r n s))
      (slice_differentiableAt m (hd_lin h2 h2c r n s)),
    pd_add n x (slice_differentiableAt n (hd_lin h1 h1c r m s))
      (slice_differentiableAt n (hd_lin h2 h2c r m s))]
  ring

/-- Vanishing of the linearized Riemann tensor on any `C³` pure-gauge perturbation
`δh_{ij} = ∂_i ξ_j + ∂_j ξ_i`. -/
lemma linRiemann_pureGauge (ξ : (Fin 4 → ℝ) → (Fin 4 → ℝ)) (x : Fin 4 → ℝ)
    (hξ : ∀ a, ContDiffAt ℝ 3 (fun z => ξ z a) x) (r s m n : Fin 4) :
    linRiemann (pureGauge ξ) x r s m n = 0 := by
  have nh : ∀ᶠ y in nhds x, ∀ a, ContDiffAt ℝ 2 (fun z => ξ z a) y := by
    rw [Filter.eventually_all]; intro a
    exact ((hξ a).of_le (by norm_num)).eventually (by simp)
  have hcongr : ∀ a b,
      (fun y => linChristoffel (pureGauge ξ) y r a b) =ᶠ[nhds x]
        fun y => eta4 r r * pd b (pd a fun z => ξ z r) y := by
    intro a b
    filter_upwards [nh] with y hy
    exact linChristoffel_pureGauge ξ y hy r a b
  rw [linRiemann, pd_congr_nhds m x (hcongr n s), pd_congr_nhds n x (hcongr m s),
    pd_const_mul, pd_const_mul]
  have hcomm1 : (fun y => pd s (pd n fun z => ξ z r) y)
      =ᶠ[nhds x] fun y => pd n (pd s fun z => ξ z r) y := by
    filter_upwards [nh] with y hy; exact pd_comm s n (hy r)
  have hcomm2 : (fun y => pd s (pd m fun z => ξ z r) y)
      =ᶠ[nhds x] fun y => pd m (pd s fun z => ξ z r) y := by
    filter_upwards [nh] with y hy; exact pd_comm s m (hy r)
  rw [pd_congr_nhds m x hcomm1, pd_congr_nhds n x hcomm2]
  have hpds : ContDiffAt ℝ 2 (pd s fun z => ξ z r) x := contDiffAt_pd s (hξ r)
  rw [pd_comm m n hpds]
  ring

/-- Linearized Riemann curvature tensor is invariant under `C³` infinitesimal diffeomorphisms
`h' = h + ∂_i ξ_j + ∂_j ξ_i`. -/
lemma linRiemann_gauge_invariant (h : (Fin 4 → ℝ) → Tensor2 4)
    (ξ : (Fin 4 → ℝ) → (Fin 4 → ℝ)) (x : Fin 4 → ℝ)
    (hh : ∀ a b, ContDiffAt ℝ 2 (fun z => h z a b) x)
    (hξ : ∀ a, ContDiffAt ℝ 3 (fun z => ξ z a) x) (r s m n : Fin 4) :
    linRiemann (gaugeTransform h ξ) x r s m n = linRiemann h x r s m n := by
  have hpg : ∀ a b, ContDiffAt ℝ 2 (fun z => pureGauge ξ z a b) x := fun a b =>
    (contDiffAt_pd a (hξ b)).add (contDiffAt_pd b (hξ a))
  have heq : gaugeTransform h ξ = fun y a b => h y a b + pureGauge ξ y a b := by
    ext y a b; simp [gaugeTransform, pureGauge, add_assoc]
  rw [heq, linRiemann_add h (pureGauge ξ) x hh hpg r s m n,
    linRiemann_pureGauge ξ x hξ r s m n, add_zero]

/-- Linearized Ricci tensor is gauge invariant under `C³` infinitesimal diffeomorphisms. -/
lemma linRicci_gauge_invariant (h : (Fin 4 → ℝ) → Tensor2 4)
    (ξ : (Fin 4 → ℝ) → (Fin 4 → ℝ)) (x : Fin 4 → ℝ)
    (hh : ∀ a b, ContDiffAt ℝ 2 (fun z => h z a b) x)
    (hξ : ∀ a, ContDiffAt ℝ 3 (fun z => ξ z a) x) (i j : Fin 4) :
    linRicci (gaugeTransform h ξ) x i j = linRicci h x i j := by
  simp only [linRicci]
  exact Finset.sum_congr rfl fun r _ => linRiemann_gauge_invariant h ξ x hh hξ r i r j

/-- Linearized Einstein tensor is gauge invariant under `C³` infinitesimal diffeomorphisms. -/
lemma linEinstein_gauge_invariant (h : (Fin 4 → ℝ) → Tensor2 4)
    (ξ : (Fin 4 → ℝ) → (Fin 4 → ℝ)) (x : Fin 4 → ℝ)
    (hh : ∀ a b, ContDiffAt ℝ 2 (fun z => h z a b) x)
    (hξ : ∀ a, ContDiffAt ℝ 3 (fun z => ξ z a) x) (i j : Fin 4) :
    linEinstein (gaugeTransform h ξ) x i j = linEinstein h x i j := by
  simp only [linEinstein, linScalar, linRicci_gauge_invariant h ξ x hh hξ]

/-!

## D. Lorenz gauge and gravitational wave propagation

-/

/-- Lorenz (harmonic/de Donder) gauge divergence vector `∂^k h̄_{kj} = η^{kk} ∂_k h̄_{kj}`. -/
noncomputable def lorenzDiv (h : (Fin 4 → ℝ) → Tensor2 4) (x : Fin 4 → ℝ) (j : Fin 4) : ℝ :=
  ∑ k : Fin 4, eta4 k k * pd k (fun y => traceReversed (h y) k j) x

/-- Lorenz gauge condition `lorenzDiv h x j = 0`. -/
def lorenzGaugeCond (h : (Fin 4 → ℝ) → Tensor2 4) (x : Fin 4 → ℝ) (j : Fin 4) : Prop :=
  lorenzDiv h x j = 0

private lemma contDiffAt_traceReversed {h : (Fin 4 → ℝ) → Tensor2 4} {x : Fin 4 → ℝ}
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

private lemma contDiffAt_hTrace {h : (Fin 4 → ℝ) → Tensor2 4} {x : Fin 4 → ℝ}
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

private lemma linChristoffel_trace (h : (Fin 4 → ℝ) → Tensor2 4) (y : Fin 4 → ℝ)
    (hsym : ∀ z a b, h z a b = h z b a)
    (hh : ∀ a b, DifferentiableAt ℝ (fun z => h z a b) y) (i : Fin 4) :
    (∑ r : Fin 4, linChristoffel h y r r i) = (1 / 2) * pd i (fun z => hTrace (h z)) y := by
  have heq : ∀ r, (fun z => h z r i) = fun z => h z i r := fun r => funext fun z => hsym z r i
  simp only [linChristoffel, heq, add_sub_cancel_right]
  have hsum : (∑ r : Fin 4, (1 / 2) * eta4 r r * pd i (fun z => h z r r) y)
      = (1 / 2) * pd i (fun z => ∑ r : Fin 4, eta4 r r * h z r r) y := by
    rw [pd_sum i (fun r z => eta4 r r * h z r r) y
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

/-- Expansion of `linRicci h x i j` in terms of `h̄ = traceReversed h` and `lorenzDiv h`. -/
lemma linRicci_in_traceReversed (h : (Fin 4 → ℝ) → Tensor2 4) (x : Fin 4 → ℝ)
    (hsym : ∀ z a b, h z a b = h z b a)
    (hh : ∀ a b, ContDiffAt ℝ 2 (fun z => h z a b) x) (i j : Fin 4) :
    linRicci h x i j = -(1 / 2) * boxEta (fun y => traceReversed (h y) i j) x
      + (1 / 2) * pd i (fun y => lorenzDiv h y j) x
      + (1 / 2) * pd j (fun y => lorenzDiv h y i) x
      + (1 / 4) * eta4 i j * boxEta (fun y => hTrace (traceReversed (h y))) x := by
  let b : (Fin 4 → ℝ) → Tensor2 4 := fun y => traceReversed (h y)
  let T : (Fin 4 → ℝ) → ℝ := fun y => hTrace (b y)
  have nh : ∀ᶠ y in nhds x, ∀ a b', ContDiffAt ℝ 2 (fun z => h z a b') y := by
    rw [Filter.eventually_all]; intro a; rw [Filter.eventually_all]; intro b'
    exact (hh a b').eventually (by simp)
  have hb_c2 : ∀ y, (∀ a b', ContDiffAt ℝ 2 (fun z => h z a b') y) →
      ∀ a b', ContDiffAt ℝ 2 (fun z => b z a b') y := fun y hy a b' =>
    contDiffAt_traceReversed hy a b'
  have hT_c2 : ∀ y, (∀ a b', ContDiffAt ℝ 2 (fun z => h z a b') y) →
      ContDiffAt ℝ 2 T y := fun y hy => contDiffAt_hTrace fun a b' => hb_c2 y hy a b'
  have hc_eq : ∀ r,
      (fun y => linChristoffel h y r j i) =ᶠ[nhds x] fun y =>
        (1 / 2) * eta4 r r * (pd i (fun z => b z r j) y
          + pd j (fun z => b z r i) y - pd r (fun z => b z j i) y)
          - (1 / 4) * eta4 r r * (eta4 r j * pd i T y + eta4 r i * pd j T y
            - eta4 j i * pd r T y) := by
    intro r
    filter_upwards [nh] with y hy
    have hcd : ∀ p q, (fun z => h z p q) = fun z =>
        b z p q - (1 / 2) * eta4 p q * T z := by
      intro p q; funext z
      have hi := congrArg (fun M => M p q) (traceReversed_involutive (h z))
      simpa [b, T, traceReversed] using hi.symm
    have d_b : ∀ p q, DifferentiableAt ℝ (fun z => b z p q) y :=
      fun p q => (hb_c2 y hy p q).differentiableAt (by norm_num)
    have d_T : DifferentiableAt ℝ T y := (hT_c2 y hy).differentiableAt (by norm_num)
    simp only [linChristoffel, hcd]
    rw [pd_sub i y (slice_differentiableAt i (d_b r j))
        ((slice_differentiableAt i d_T).const_mul _),
      pd_sub j y (slice_differentiableAt j (d_b r i))
        ((slice_differentiableAt j d_T).const_mul _),
      pd_sub r y (slice_differentiableAt r (d_b j i))
        ((slice_differentiableAt r d_T).const_mul _),
      pd_const_mul, pd_const_mul, pd_const_mul]
    ring
  have hb_at : ∀ p q, ContDiffAt ℝ 2 (fun z => b z p q) x := hb_c2 x hh
  have hT_at : ContDiffAt ℝ 2 T x := hT_c2 x hh
  have hterm : ∀ r, pd r (fun y => linChristoffel h y r j i) x =
      (1 / 2) * eta4 r r * pd i (pd r fun z => b z r j) x
      + (1 / 2) * eta4 r r * pd j (pd r fun z => b z r i) x
      - (1 / 2) * eta4 r r * pd r (pd r fun z => b z j i) x
      - (1 / 4) * (eta4 r r * eta4 r j) * pd i (pd r T) x
      - (1 / 4) * (eta4 r r * eta4 r i) * pd j (pd r T) x
      + (1 / 4) * eta4 j i * (eta4 r r * pd r (pd r T) x) := by
    intro r
    have db : ∀ p q μ, DifferentiableAt ℝ (pd μ fun z => b z p q) x :=
      fun p q μ => pd_differentiableAt μ (hb_at p q)
    have dT : ∀ μ, DifferentiableAt ℝ (pd μ T) x := fun μ => pd_differentiableAt μ hT_at
    have h1 : DifferentiableAt ℝ (fun y => (1 / 2 : ℝ) * eta4 r r *
        (pd i (fun z => b z r j) y + pd j (fun z => b z r i) y - pd r (fun z => b z j i) y)) x :=
      (((db r j i).add (db r i j)).sub (db j i r)).const_mul _
    have h2 : DifferentiableAt ℝ (fun y => (1 / 4 : ℝ) * eta4 r r *
        (eta4 r j * pd i T y + eta4 r i * pd j T y - eta4 j i * pd r T y)) x :=
      ((((dT i).const_mul _).add ((dT j).const_mul _)).sub ((dT r).const_mul _)).const_mul _
    have d1 : DifferentiableAt ℝ (fun s => pd i (fun z => b z r j) (Function.update x r s))
        (x r) := slice_differentiableAt r (db r j i)
    have d2 : DifferentiableAt ℝ (fun s => pd j (fun z => b z r i) (Function.update x r s))
        (x r) := slice_differentiableAt r (db r i j)
    have d3 : DifferentiableAt ℝ (fun s => pd r (fun z => b z j i) (Function.update x r s))
        (x r) := slice_differentiableAt r (db j i r)
    have dt1 : DifferentiableAt ℝ (fun s => eta4 r j * pd i T (Function.update x r s)) (x r) :=
      (slice_differentiableAt r (dT i)).const_mul _
    have dt2 : DifferentiableAt ℝ (fun s => eta4 r i * pd j T (Function.update x r s)) (x r) :=
      (slice_differentiableAt r (dT j)).const_mul _
    have dt3 : DifferentiableAt ℝ (fun s => eta4 j i * pd r T (Function.update x r s)) (x r) :=
      (slice_differentiableAt r (dT r)).const_mul _
    rw [pd_congr_nhds r x (hc_eq r), pd_sub r x (slice_differentiableAt r h1)
        (slice_differentiableAt r h2), pd_const_mul, pd_const_mul,
      pd_sub r x (d1.add d2) d3, pd_add r x d1 d2,
      pd_sub r x (dt1.add dt2) dt3, pd_add r x dt1 dt2,
      pd_const_mul, pd_const_mul, pd_const_mul,
      pd_comm r i (hb_at r j), pd_comm r j (hb_at r i), pd_comm r i hT_at, pd_comm r j hT_at]
    ring
  have hdiv_j : pd i (fun y => lorenzDiv h y j) x
      = ∑ r : Fin 4, eta4 r r * pd i (pd r fun z => b z r j) x := by
    simp only [lorenzDiv]
    rw [pd_sum i _ x fun r =>
      slice_differentiableAt i ((pd_differentiableAt r (hb_at r j)).const_mul _)]
    refine Finset.sum_congr rfl fun r _ => pd_const_mul i (eta4 r r) x
  have hdiv_i : pd j (fun y => lorenzDiv h y i) x
      = ∑ r : Fin 4, eta4 r r * pd j (pd r fun z => b z r i) x := by
    simp only [lorenzDiv]
    rw [pd_sum j _ x fun r =>
      slice_differentiableAt j ((pd_differentiableAt r (hb_at r i)).const_mul _)]
    refine Finset.sum_congr rfl fun r _ => pd_const_mul j (eta4 r r) x
  have hbox_sym : boxEta (fun y => b y j i) x = boxEta (fun y => b y i j) x := by
    have hbs : (fun y => b y j i) = fun y => b y i j :=
      funext fun y => traceReversed_symm (hsym y) j i
    simp [hbs]
  have hT_sub_j : (∑ r : Fin 4, (1 / 4 : ℝ) * (eta4 r r * eta4 r j) * pd i (pd r T) x)
      = (1 / 4) * pd i (pd j T) x := by
    fin_cases j <;> simp [Fin.sum_univ_four, eta4]
  have hT_sub_i : (∑ r : Fin 4, (1 / 4 : ℝ) * (eta4 r r * eta4 r i) * pd j (pd r T) x)
      = (1 / 4) * pd j (pd i T) x := by
    fin_cases i <;> simp [Fin.sum_univ_four, eta4]
  have hT_comm : pd j (pd i T) x = pd i (pd j T) x := pd_comm j i hT_at
  simp only [linRicci, linRiemann, Finset.sum_sub_distrib, hterm,
    pd_linChristoffel_diag h x hsym hh i j, Finset.sum_add_distrib, ← Finset.mul_sum]
  change _ = -(1 / 2) * boxEta (fun y => b y i j) x
      + (1 / 2) * pd i (fun y => lorenzDiv h y j) x
      + (1 / 2) * pd j (fun y => lorenzDiv h y i) x
      + (1 / 4) * eta4 i j * boxEta T x
  rw [hdiv_j, hdiv_i, ← hbox_sym, eta4_symm j i, hT_sub_j, hT_sub_i, hT_comm]
  have hs1 : (∑ r : Fin 4, (1 / 2 : ℝ) * eta4 r r * pd i (pd r fun z => b z r j) x)
      = (1 / 2) * ∑ r : Fin 4, eta4 r r * pd i (pd r fun z => b z r j) x := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun _ _ => by ring
  have hs2 : (∑ r : Fin 4, (1 / 2 : ℝ) * eta4 r r * pd j (pd r fun z => b z r i) x)
      = (1 / 2) * ∑ r : Fin 4, eta4 r r * pd j (pd r fun z => b z r i) x := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun _ _ => by ring
  have hs3 : (∑ r : Fin 4, (1 / 2 : ℝ) * eta4 r r * pd r (pd r fun z => b z j i) x)
      = (1 / 2) * boxEta (fun y => b y j i) x := by
    simp only [boxEta, Finset.mul_sum]
    refine Finset.sum_congr rfl fun _ _ => by ring
  rw [hs1, hs2, hs3]
  simp only [boxEta]
  ring

private lemma linScalar_in_traceReversed (h : (Fin 4 → ℝ) → Tensor2 4) (x : Fin 4 → ℝ)
    (hsym : ∀ z a b, h z a b = h z b a)
    (hh : ∀ a b, ContDiffAt ℝ 2 (fun z => h z a b) x) :
    linScalar h x = (1 / 2) * boxEta (fun y => hTrace (traceReversed (h y))) x
      + ∑ a : Fin 4, eta4 a a * pd a (fun y => lorenzDiv h y a) x := by
  let b : (Fin 4 → ℝ) → Tensor2 4 := fun y => traceReversed (h y)
  let T : (Fin 4 → ℝ) → ℝ := fun y => hTrace (b y)
  have hb_at : ∀ p q, ContDiffAt ℝ 2 (fun z => b z p q) x := fun p q =>
    contDiffAt_traceReversed hh p q
  have hbox_trace : (∑ i : Fin 4, eta4 i i * boxEta (fun y => b y i i) x) = boxEta T x := by
    simp only [boxEta, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun μ _ => ?_
    have hdμ : ∀ i, DifferentiableAt ℝ (pd μ fun y => b y i i) x :=
      fun i => pd_differentiableAt μ (hb_at i i)
    have hcongr : (fun y => ∑ i : Fin 4, eta4 i i * b y i i) = T := rfl
    have hpd1 : ∀ y, (∀ i, DifferentiableAt ℝ (fun z => b z i i) y) →
        pd μ T y = ∑ i : Fin 4, eta4 i i * pd μ (fun z => b z i i) y := by
      intro y hy
      rw [← hcongr, pd_sum μ _ y fun i => (slice_differentiableAt μ (hy i)).const_mul _]
      refine Finset.sum_congr rfl fun i _ => pd_const_mul μ (eta4 i i) y
    have nh : ∀ᶠ y in nhds x, ∀ a b', ContDiffAt ℝ 2 (fun z => h z a b') y := by
      rw [Filter.eventually_all]; intro a; rw [Filter.eventually_all]; intro b'
      exact (hh a b').eventually (by simp)
    have hev : pd μ T =ᶠ[nhds x] fun y => ∑ i : Fin 4, eta4 i i * pd μ (fun z => b z i i) y := by
      filter_upwards [nh] with y hy
      exact hpd1 y fun i => (contDiffAt_traceReversed hy i i).differentiableAt (by norm_num)
    rw [pd_congr_nhds μ x hev,
      pd_sum μ _ x fun i => slice_differentiableAt μ ((hdμ i).const_mul _),
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [pd_const_mul, mul_left_comm]
  have heta_sq : (∑ i : Fin 4, eta4 i i * eta4 i i) = 4 := by
    simp [Fin.sum_univ_four, eta4]
    norm_num
  simp only [linScalar, linRicci_in_traceReversed h x hsym hh, mul_add,
    Finset.sum_add_distrib]
  have h1 : (∑ i : Fin 4, eta4 i i * (-(1 / 2) * boxEta (fun y => b y i i) x))
      = -(1 / 2) * boxEta T x := by
    calc (∑ i : Fin 4, eta4 i i * (-(1 / 2) * boxEta (fun y => b y i i) x))
        = -(1 / 2) * ∑ i : Fin 4, eta4 i i * boxEta (fun y => b y i i) x := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun _ _ => by ring
      _ = -(1 / 2) * boxEta T x := by rw [hbox_trace]
  have h4 : (∑ i : Fin 4, eta4 i i * ((1 / 4) * eta4 i i * boxEta T x))
      = boxEta T x := by
    calc (∑ i : Fin 4, eta4 i i * ((1 / 4) * eta4 i i * boxEta T x))
        = (1 / 4) * (∑ i : Fin 4, eta4 i i * eta4 i i) * boxEta T x := by
          rw [Finset.mul_sum, Finset.sum_mul]; refine Finset.sum_congr rfl fun _ _ => by ring
      _ = boxEta T x := by rw [heta_sq]; ring
  change (∑ i : Fin 4, eta4 i i * (-(1 / 2) * boxEta (fun y => b y i i) x))
      + (∑ i : Fin 4, eta4 i i * ((1 / 2) * pd i (fun y => lorenzDiv h y i) x))
      + (∑ i : Fin 4, eta4 i i * ((1 / 2) * pd i (fun y => lorenzDiv h y i) x))
      + (∑ i : Fin 4, eta4 i i * ((1 / 4) * eta4 i i * boxEta T x))
      = (1 / 2) * boxEta T x + ∑ a : Fin 4, eta4 a a * pd a (fun y => lorenzDiv h y a) x
  rw [h1, h4]
  have h2 : (∑ i : Fin 4, eta4 i i * ((1 / 2) * pd i (fun y => lorenzDiv h y i) x))
      = (1 / 2) * ∑ a : Fin 4, eta4 a a * pd a (fun y => lorenzDiv h y a) x := by
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
      - (1 / 2) * eta4 i j * ∑ a : Fin 4, eta4 a a * pd a (fun y => lorenzDiv h y a) x := by
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

/-!

## E. Transverse-traceless modes and Newtonian limit

-/

/-- Transverse-traceless (`TT`) plane gravitational wave propagating along the `+z` direction
with wave profile `f(t - z)` and `+`, `×` polarization amplitudes `hPlus`, `hCross`. -/
noncomputable def ttWave (hPlus hCross : ℝ) (f : ℝ → ℝ) (x : Fin 4 → ℝ) : Tensor2 4 :=
  let w := f (x 0 - x 3)
  fun i j =>
    if i = 1 ∧ j = 1 then hPlus * w
    else if i = 2 ∧ j = 2 then -(hPlus * w)
    else if (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1) then hCross * w
    else 0

/-- Symmetry of `ttWave`. -/
lemma ttWave_symm (hPlus hCross : ℝ) (f : ℝ → ℝ) (x : Fin 4 → ℝ) :
    IsSymm (ttWave hPlus hCross f x) := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [ttWave]

/-- A `TT` gravitational wave is trace-free: `η^{ij} h^{TT}_{ij} = 0`. -/
lemma ttWave_trace_zero (hPlus hCross : ℝ) (f : ℝ → ℝ) (x : Fin 4 → ℝ) :
    hTrace (ttWave hPlus hCross f x) = 0 := by
  simp [hTrace, ttWave, Fin.sum_univ_four, eta4]

/-- Trace reversal acts trivially on `ttWave`. -/
lemma traceReversed_ttWave (hPlus hCross : ℝ) (f : ℝ → ℝ) (x : Fin 4 → ℝ) :
    traceReversed (ttWave hPlus hCross f x) = ttWave hPlus hCross f x := by
  ext i j
  simp [traceReversed, ttWave_trace_zero]

private lemma pd_1_wave (c : ℝ) (f : ℝ → ℝ) (x : Fin 4 → ℝ) :
    pd 1 (fun y => c * f (y 0 - y 3)) x = 0 := by
  have hfn : (fun s => c * f (Function.update x 1 s 0 - Function.update x 1 s 3))
      = fun _ => c * f (x 0 - x 3) := by funext s; simp
  rw [pd, hfn, deriv_const']

private lemma pd_2_wave (c : ℝ) (f : ℝ → ℝ) (x : Fin 4 → ℝ) :
    pd 2 (fun y => c * f (y 0 - y 3)) x = 0 := by
  have hfn : (fun s => c * f (Function.update x 2 s 0 - Function.update x 2 s 3))
      = fun _ => c * f (x 0 - x 3) := by funext s; simp
  rw [pd, hfn, deriv_const']

/-- A `TT` wave automatically satisfies the Lorenz gauge condition `∂^k h^{TT}_{kj} = 0`
for any wave profile `f`. -/
lemma ttWave_lorenz_gauge (hPlus hCross : ℝ) (f : ℝ → ℝ) (x : Fin 4 → ℝ) (j : Fin 4) :
    lorenzGaugeCond (ttWave hPlus hCross f) x j := by
  have htr : ∀ y, traceReversed (ttWave hPlus hCross f y) = ttWave hPlus hCross f y :=
    traceReversed_ttWave hPlus hCross f
  have hc0 : ∀ μ, pd μ (fun _ : Fin 4 → ℝ => (0 : ℝ)) x = 0 := fun μ => pd_const μ 0 x
  have h1neg : pd 2 (fun y => -(hPlus * f (y 0 - y 3))) x = 0 := by
    have hfun : (fun y : Fin 4 → ℝ => -(hPlus * f (y 0 - y 3)))
        = fun y => (-hPlus) * f (y 0 - y 3) := funext fun y => by ring
    rw [hfun, pd_2_wave]
  simp only [lorenzGaugeCond, lorenzDiv, htr, Fin.sum_univ_four, eta4]
  fin_cases j <;>
    simp only [ttWave] <;> norm_num
  · simp [hc0]
  · simp [hc0, pd_1_wave, pd_2_wave]
  · simp [hc0, pd_1_wave, h1neg]
  · simp [hc0]

private lemma pd_0_wave (c : ℝ) (f : ℝ → ℝ) (hf : Differentiable ℝ f) (x : Fin 4 → ℝ) :
    pd 0 (fun y => c * f (y 0 - y 3)) x = c * deriv f (x 0 - x 3) := by
  have hfun : (fun s => c * f (Function.update x 0 s 0 - Function.update x 0 s 3))
      = fun s => c * f (s - x 3) := by funext s; simp
  have hsub : HasDerivAt (fun s => s - x 3) 1 (x 0) := by
    simpa using (hasDerivAt_id (x 0)).sub_const (x 3)
  have hd : HasDerivAt (fun s => c * f (s - x 3)) (c * deriv f (x 0 - x 3)) (x 0) := by
    simpa using ((hf (x 0 - x 3)).hasDerivAt.comp (x 0) hsub).const_mul c
  rw [pd, hfun, hd.deriv]

private lemma pd_3_wave (c : ℝ) (f : ℝ → ℝ) (hf : Differentiable ℝ f) (x : Fin 4 → ℝ) :
    pd 3 (fun y => c * f (y 0 - y 3)) x = -(c * deriv f (x 0 - x 3)) := by
  have hfun : (fun s => c * f (Function.update x 3 s 0 - Function.update x 3 s 3))
      = fun s => c * f (x 0 - s) := by funext s; simp
  have hsub : HasDerivAt (fun s => x 0 - s) (-1) (x 3) :=
    ((hasDerivAt_const (x 3) (x 0)).sub (hasDerivAt_id (x 3))).congr_deriv (by ring)
  have hd0 : HasDerivAt (fun s => f (x 0 - s)) (deriv f (x 0 - x 3) * (-1)) (x 3) :=
    (hf (x 0 - x 3)).hasDerivAt.comp (x 3) hsub
  have hd : HasDerivAt (fun s => c * f (x 0 - s)) (-(c * deriv f (x 0 - x 3))) (x 3) :=
    (hd0.const_mul c).congr_deriv (by ring)
  rw [pd, hfun, hd.deriv]

private lemma boxEta_zero (x : Fin 4 → ℝ) : boxEta (fun _ : Fin 4 → ℝ => (0 : ℝ)) x = 0 := by
  have hpd : ∀ μ : Fin 4, pd μ (fun _ : Fin 4 → ℝ => (0 : ℝ)) = fun _ => 0 :=
    fun μ => funext fun y => pd_const μ 0 y
  simp only [boxEta, hpd, pd_const, mul_zero, Finset.sum_const_zero]

private lemma boxEta_wave (c : ℝ) (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (x : Fin 4 → ℝ) :
    boxEta (fun y => c * f (y 0 - y 3)) x = 0 := by
  have hf1 : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hf2 : Differentiable ℝ (deriv f) :=
    ((contDiff_succ_iff_deriv (n := 1)).mp hf).2.2.differentiable (by norm_num)
  have h0eq : pd (0 : Fin 4) (fun y : Fin 4 → ℝ => c * f (y 0 - y 3))
      = fun y => c * deriv f (y 0 - y 3) :=
    funext fun y => pd_0_wave c f hf1 y
  have h3eq : pd (3 : Fin 4) (fun y : Fin 4 → ℝ => c * f (y 0 - y 3))
      = fun y => (-c) * deriv f (y 0 - y 3) := by
    funext y
    rw [pd_3_wave c f hf1 y]
    ring
  have hc1 : pd (1 : Fin 4) (fun y : Fin 4 → ℝ => c * f (y 0 - y 3)) = fun _ => 0 :=
    funext fun y => pd_1_wave c f y
  have hc2 : pd (2 : Fin 4) (fun y : Fin 4 → ℝ => c * f (y 0 - y 3)) = fun _ => 0 :=
    funext fun y => pd_2_wave c f y
  simp only [boxEta, Fin.sum_univ_four, eta4, h0eq, hc1, hc2, h3eq]
  rw [pd_0_wave c (deriv f) hf2 x, pd_3_wave (-c) (deriv f) hf2 x, pd_const, pd_const]
  norm_num

private lemma contDiffAt_wave (c : ℝ) (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (x : Fin 4 → ℝ) :
    ContDiffAt ℝ 2 (fun y => c * f (y 0 - y 3)) x := by
  have hlin : ContDiff ℝ 2 (fun y : Fin 4 → ℝ => y 0 - y 3) :=
    (contDiff_pi.mp (contDiff_id (𝕜 := ℝ) (E := Fin 4 → ℝ)) 0).sub
      (contDiff_pi.mp (contDiff_id (𝕜 := ℝ) (E := Fin 4 → ℝ)) 3)
  exact contDiffAt_const.mul (hf.comp hlin).contDiffAt

/-- Every transverse-traceless gravitational wave with `C²` profile `f` satisfies the linearized
vacuum Einstein equations `G^{(1)}_{ij} = 0`. -/
lemma ttWave_linEinstein_zero (hPlus hCross : ℝ) (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f)
    (x : Fin 4 → ℝ) (i j : Fin 4) :
    linEinstein (ttWave hPlus hCross f) x i j = 0 := by
  have hsym : ∀ z a b, ttWave hPlus hCross f z a b = ttWave hPlus hCross f z b a :=
    ttWave_symm hPlus hCross f
  have hc : ∀ a b, ContDiffAt ℝ 2 (fun z => ttWave hPlus hCross f z a b) x := by
    intro a b
    fin_cases a <;> fin_cases b <;> simp only [ttWave] <;> norm_num
    all_goals first
      | exact contDiffAt_const
      | exact contDiffAt_wave hPlus f hf x
      | exact (contDiffAt_wave hPlus f hf x).neg
      | exact contDiffAt_wave hCross f hf x
  have hlz : ∀ᶠ y in nhds x, ∀ k, lorenzGaugeCond (ttWave hPlus hCross f) y k :=
    Filter.Eventually.of_forall fun y k => ttWave_lorenz_gauge hPlus hCross f y k
  rw [linEinstein_lorenz_gauge (ttWave hPlus hCross f) x hsym hc hlz i j]
  have htr : (fun y => traceReversed (ttWave hPlus hCross f y) i j)
      = fun y => ttWave hPlus hCross f y i j := by
    funext y; simp [traceReversed_ttWave]
  rw [htr]
  fin_cases i <;> fin_cases j <;> simp only [ttWave] <;> norm_num
  all_goals first
    | exact boxEta_zero x
    | exact boxEta_wave hPlus f hf x
    | (rw [show (fun y : Fin 4 → ℝ => -(hPlus * f (y 0 - y 3)))
          = fun y => (-hPlus) * f (y 0 - y 3) from funext fun _ => by ring];
        exact boxEta_wave (-hPlus) f hf x)
    | exact boxEta_wave hCross f hf x

/-- Weak-field isotropic Newtonian metric perturbation `h_{ij} = -2 Φ δ_{ij}` corresponding to
`ds² = -(1 + 2 Φ) dt² + (1 - 2 Φ) d𝐱²` in `(-, +, +, +)` signature. -/
noncomputable def newtonianPerturb (Φ : (Fin 4 → ℝ) → ℝ) (x : Fin 4 → ℝ) : Tensor2 4 :=
  fun i j => if i = j then -(2 * Φ x) else 0

/-- Symmetry of `newtonianPerturb`. -/
lemma newtonianPerturb_symm (Φ : (Fin 4 → ℝ) → ℝ) (x : Fin 4 → ℝ) :
    IsSymm (newtonianPerturb Φ x) := by
  intro i j; fin_cases i <;> fin_cases j <;> simp [newtonianPerturb]

/-- Trace reversal isolates the `(0, 0)` component: `h̄_{00} = -4 Φ`, all other entries `0`. -/
lemma traceReversed_newtonianPerturb (Φ : (Fin 4 → ℝ) → ℝ) (x : Fin 4 → ℝ) (i j : Fin 4) :
    traceReversed (newtonianPerturb Φ x) i j = if i = 0 ∧ j = 0 then -(4 * Φ x) else 0 := by
  have hT : hTrace (newtonianPerturb Φ x) = -(4 * Φ x) := by
    simp [hTrace, newtonianPerturb, Fin.sum_univ_four, eta4]; ring
  fin_cases i <;> fin_cases j <;> simp [traceReversed, hT, newtonianPerturb, eta4] <;> ring

/-- Static Newtonian potentials (`∂_0 Φ = 0`) satisfy the Lorenz gauge identically. -/
lemma newtonianPerturb_lorenz_gauge (Φ : (Fin 4 → ℝ) → ℝ) (y : Fin 4 → ℝ)
    (hstat : pd 0 Φ y = 0) (j : Fin 4) :
    lorenzGaugeCond (newtonianPerturb Φ) y j := by
  simp only [lorenzGaugeCond, lorenzDiv, Fin.sum_univ_four, traceReversed_newtonianPerturb, eta4]
  fin_cases j <;> norm_num
  · simp only [pd_const]
    have hneg : (fun z => -(4 * Φ z)) = fun z => (-4 : ℝ) * Φ z := funext fun _ => by ring
    rw [hneg, pd_const_mul, hstat]
    ring
  all_goals simp [pd_const]

/-- Three-dimensional spatial Laplacian `∇² Φ = ∂₁² Φ + ∂₂² Φ + ∂₃² Φ`. -/
noncomputable def laplacian3 (Φ : (Fin 4 → ℝ) → ℝ) (x : Fin 4 → ℝ) : ℝ :=
  pd 1 (pd 1 Φ) x + pd 2 (pd 2 Φ) x + pd 3 (pd 3 Φ) x

/-- Weak-field Newtonian limit: for a static `C²` potential `Φ`, the `(0, 0)` linearized Einstein
tensor equals `2 ∇² Φ`, so `G^{(1)}_{00} = 8 π ρ ↔ ∇² Φ = 4 π ρ`. -/
lemma newtonianPerturb_linEinstein_00 (Φ : (Fin 4 → ℝ) → ℝ) (x : Fin 4 → ℝ)
    (hΦ : ContDiffAt ℝ 2 Φ x) (hstat : ∀ y, pd 0 Φ y = 0) :
    linEinstein (newtonianPerturb Φ) x 0 0 = 2 * laplacian3 Φ x := by
  have hsym : ∀ z a b, newtonianPerturb Φ z a b = newtonianPerturb Φ z b a :=
    newtonianPerturb_symm Φ
  have hc : ∀ a b, ContDiffAt ℝ 2 (fun z => newtonianPerturb Φ z a b) x := fun a b => by
    fin_cases a <;> fin_cases b <;> simp only [newtonianPerturb, ↓reduceIte]
    all_goals first | exact contDiffAt_const | exact (contDiffAt_const.mul hΦ).neg
  have hlz : ∀ᶠ y in nhds x, ∀ k, lorenzGaugeCond (newtonianPerturb Φ) y k :=
    Filter.Eventually.of_forall fun y k => newtonianPerturb_lorenz_gauge Φ y (hstat y) k
  rw [linEinstein_lorenz_gauge (newtonianPerturb Φ) x hsym hc hlz 0 0]
  have htr : (fun y => traceReversed (newtonianPerturb Φ y) 0 0)
      = fun y => (-4 : ℝ) * Φ y := by
    funext y; simp only [traceReversed_newtonianPerturb, and_self, ↓reduceIte]; ring
  have h00 : pd 0 (pd 0 (fun y => (-4 : ℝ) * Φ y)) x = 0 := by
    have hev : pd 0 (fun y => (-4 : ℝ) * Φ y) = fun _ => 0 := funext fun z => by
      rw [pd_const_mul, hstat z, mul_zero]
    rw [hev]; exact pd_const 0 0 x
  have hk : ∀ k : Fin 4, pd k (pd k (fun y => (-4 : ℝ) * Φ y)) x
      = (-4 : ℝ) * pd k (pd k Φ) x := by
    intro k
    have hev : pd k (fun y => (-4 : ℝ) * Φ y) = fun z => (-4 : ℝ) * pd k Φ z :=
      funext fun z => pd_const_mul k (-4) z
    rw [hev, pd_const_mul]
  rw [htr]
  simp only [boxEta, Fin.sum_univ_four, eta4, laplacian3]
  rw [h00, hk 1, hk 2, hk 3]
  norm_num
  ring

/-- Equivalence between `G^{(1)}_{00} = 8 π ρ` and the Newtonian Poisson equation
`∇² Φ = 4 π ρ`. -/
lemma newtonianPerturb_poisson_iff (Φ : (Fin 4 → ℝ) → ℝ) (x : Fin 4 → ℝ)
    (hΦ : ContDiffAt ℝ 2 Φ x) (hstat : ∀ y, pd 0 Φ y = 0) (ρ : ℝ) :
    linEinstein (newtonianPerturb Φ) x 0 0 = 8 * Real.pi * ρ
      ↔ laplacian3 Φ x = 4 * Real.pi * ρ := by
  rw [newtonianPerturb_linEinstein_00 Φ x hΦ hstat]
  constructor <;> intro h <;> linarith

end Linearized

end GeneralRelativity
