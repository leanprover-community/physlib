/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Data.Set.Basic
public import Physlib.SpaceAndTime.SpaceTime.Derivatives
public import PhyslibAlpha.Relativity.Metrics.Minkowski
public import PhyslibAlpha.Relativity.Tensors.EinsteinTensor
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Ring

/-!

# Coordinate metrics and the differential curvature pipeline

Coordinate-chart metric fields (`CoordinateMetric`) and the differential pipeline computing
Christoffel symbols, Riemann, Ricci, scalar, and Einstein tensors from metric components.

## i. Overview

A `CoordinateMetric n` packages a coordinate-dependent symmetric metric field `g`, its inverse
`ginv`, and the regular chart domain on which `g` and `ginv` are two-sided inverses. From any
coordinate metric and inverse pair `(g, ginv)`, `Pipeline` defines coordinate partial derivatives
`pd μ f x` along each coordinate axis and builds the full differential chain:

`g ↦ ∂g ↦ Γ^k_{ij} ↦ ∂Γ ↦ R^ρ_{σμν} ↦ Ric_{σν} ↦ S ↦ G_{ij}`.

It also provides `riemannFromData`, taking the Christoffel symbols and their partial derivatives
as explicit parameters, and proves that every constant metric has vanishing Christoffel symbols,
curvature, Ricci tensor, scalar curvature, and Einstein tensor as computed outputs of the
pipeline.

## ii. Key results

- `CoordinateMetric`, `CoordinateMetric.metricTensor` : coordinate metric field bundled with its
  regular domain and two-sided inverse proofs.
- `Pipeline.pd`, `Pipeline.pd_eq_spaceTime_deriv`, `Pipeline.pd_comm` : coordinate partial
  derivative along index `μ`, bridge to `SpaceTime.deriv`, and Schwarz commutativity.
- `Pipeline.christoffel`, `Pipeline.riemann`, `Pipeline.ricciTensorOf`, `Pipeline.ricciScalarOf`,
  `Pipeline.einsteinTensorOf` : coordinate pipeline from metric fields to the Einstein tensor.
- `Pipeline.christoffel_const`, `Pipeline.riemann_const`, `Pipeline.ricciTensorOf_const`,
  `Pipeline.ricciScalarOf_const`, `Pipeline.einsteinTensorOf_const` : vanishing of all pipeline
  outputs
  for any constant metric.
- `Pipeline.riemannFromData`, `Pipeline.riemann_eq_riemannFromData` : data-parameterised Riemann
  evaluator and definitional equality with `riemann`.

## iii. Table of contents

- A. Coordinate metric bundles
- B. Coordinate partial derivatives and metric pipeline
- C. Flatness of constant metrics
- D. Curvature from Christoffel data

## iv. References

* R. M. Wald, *General Relativity* (1984). [ref: wald_1984_general_relativity]
* C. W. Misner, K. S. Thorne, and J. A. Wheeler, *Gravitation* (1973). [ref: mtw_1973_gravitation]
* B. O'Neill, *Semi-Riemannian Geometry With Applications to Relativity* (1983).
  [ref: oneill_1983_semi_riemannian]

-/

@[expose] public section

namespace GeneralRelativity

/-!

## A. Coordinate metric bundles

-/

/-- A coordinate-chart metric field `g` paired with its inverse `ginv` and regularity domain. -/
structure CoordinateMetric (n : ℕ) where
  /-- The covariant metric component field `g_{ij}(x)`. -/
  g : (Fin n → ℝ) → Tensor2 n
  /-- The contravariant inverse metric component field `g^{ij}(x)`. -/
  ginv : (Fin n → ℝ) → Tensor2 n
  /-- Regular coordinate domain where `g` is nondegenerate. -/
  domain : Set (Fin n → ℝ)
  /-- Symmetry of the covariant metric at every point. -/
  symm : ∀ x, IsSymm (g x)
  /-- Left-to-right inverse relation `g(x) * ginv(x) = 1` on `domain`. -/
  inv_left : ∀ x ∈ domain, g x * ginv x = 1
  /-- Right-to-left inverse relation `ginv(x) * g(x) = 1` on `domain`. -/
  inv_right : ∀ x ∈ domain, ginv x * g x = 1

/-- Package a `CoordinateMetric` at a regular point `x ∈ C.domain` as a `MetricTensor`. -/
def CoordinateMetric.metricTensor {n : ℕ} (C : CoordinateMetric n) (x : Fin n → ℝ)
    (hx : x ∈ C.domain) : MetricTensor n where
  g := C.g x
  ginv := C.ginv x
  symm := C.symm x
  inv_left := C.inv_left x hx
  inv_right := C.inv_right x hx

namespace Pipeline

/-!

## B. Coordinate partial derivatives and metric pipeline

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

/-- Agreement of partial derivatives for locally equal functions on a neighborhood of `x`. -/
lemma pd_congr_nhds {n : ℕ} (μ : Fin n) {f g : (Fin n → ℝ) → ℝ} (x : Fin n → ℝ)
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
lemma pd_eq_fderiv {n : ℕ} {f : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ} {μ : Fin n}
    (hf : DifferentiableAt ℝ f x) :
    pd μ f x = fderiv ℝ f x (Pi.single μ 1) := by
  have hupd : (fun s : ℝ => Function.update x μ s)
      = fun s => x + (s - x μ) • (Pi.single μ 1 : Fin n → ℝ) := by
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

/-- Coordinate partial derivatives on `Fin 4 → ℝ` agree with `Physlib`'s `SpaceTime.deriv` (`∂_`)
under the standard index equivalence `finSumFinEquiv : Fin 1 ⊕ Fin 3 ≃ Fin 4`. -/
lemma pd_eq_spaceTime_deriv {f : SpaceTime 3 → ℝ} (μ : Fin 1 ⊕ Fin 3) (y : SpaceTime 3)
    (hf : DifferentiableAt ℝ f y) :
    pd (finSumFinEquiv μ) (fun x : Fin 4 → ℝ => f (fun α => x (finSumFinEquiv α)))
        (fun k => y (finSumFinEquiv.symm k)) =
      SpaceTime.deriv μ f y := by
  let e : Fin 1 ⊕ Fin 3 ≃ Fin 4 := finSumFinEquiv
  let L : (Fin 4 → ℝ) →L[ℝ] SpaceTime 3 :=
    LinearMap.toContinuousLinearMap
      { toFun := fun x α => x (e α)
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
  have hLsingle : L (Pi.single (e μ) (1 : ℝ) : Fin 4 → ℝ) = Lorentz.Vector.basis μ := by
    ext ν
    change (Pi.single (e μ) (1 : ℝ) : Fin 4 → ℝ) (e ν) = Lorentz.Vector.basis μ ν
    simp [Pi.single_apply, e.injective.eq_iff, eq_comm]
  have hx : L (fun k => y (e.symm k)) = y := by
    ext α; simp [L, e]
  have hcomp : HasFDerivAt (f ∘ L) ((fderiv ℝ f y).comp L) (fun k => y (e.symm k)) := by
    have hy : HasFDerivAt f (fderiv ℝ f y) (L (fun k => y (e.symm k))) := by
      rw [hx]; exact hf.hasFDerivAt
    exact hy.comp _ L.hasFDerivAt
  change pd (e μ) (f ∘ L) (fun k => y (e.symm k)) = SpaceTime.deriv μ f y
  rw [pd_eq_fderiv hcomp.differentiableAt, hcomp.fderiv, ContinuousLinearMap.comp_apply, hLsingle]
  rfl

/-- Schwarz symmetry of mixed second coordinate partial derivatives for `ContDiffAt ℝ 2`
fields. -/
lemma pd_comm {n : ℕ} {f : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ} (μ ν : Fin n)
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
lemma pd_add {n : ℕ} (μ : Fin n) {f g : (Fin n → ℝ) → ℝ} (x : Fin n → ℝ)
    (hf : DifferentiableAt ℝ (fun s => f (Function.update x μ s)) (x μ))
    (hg : DifferentiableAt ℝ (fun s => g (Function.update x μ s)) (x μ)) :
    pd μ (fun y => f y + g y) x = pd μ f x + pd μ g x :=
  deriv_add hf hg

/-- Linearity of `pd` under pointwise subtraction of differentiable coordinate slices. -/
lemma pd_sub {n : ℕ} (μ : Fin n) {f g : (Fin n → ℝ) → ℝ} (x : Fin n → ℝ)
    (hf : DifferentiableAt ℝ (fun s => f (Function.update x μ s)) (x μ))
    (hg : DifferentiableAt ℝ (fun s => g (Function.update x μ s)) (x μ)) :
    pd μ (fun y => f y - g y) x = pd μ f x - pd μ g x :=
  deriv_sub hf hg

/-- Linearity of `pd` under constant scalar multiplication. -/
lemma pd_const_mul {n : ℕ} (μ : Fin n) (c : ℝ) {f : (Fin n → ℝ) → ℝ} (x : Fin n → ℝ) :
    pd μ (fun y => c * f y) x = c * pd μ f x := by
  simp only [pd]
  exact deriv_const_mul_field c

/-- Linearity of `pd` over finite `Fin m` sums of differentiable slices. -/
lemma pd_sum {n m : ℕ} (μ : Fin n) (F : Fin m → (Fin n → ℝ) → ℝ) (x : Fin n → ℝ)
    (hF : ∀ k, DifferentiableAt ℝ (fun s => F k (Function.update x μ s)) (x μ)) :
    pd μ (fun y => ∑ k : Fin m, F k y) x = ∑ k : Fin m, pd μ (F k) x := by
  have hs : (fun s => ∑ k : Fin m, F k (Function.update x μ s))
      = ∑ k : Fin m, fun s => F k (Function.update x μ s) := by
    funext s; simp only [Finset.sum_apply]
  simp only [pd, hs]
  exact deriv_sum fun k _ => hF k

/-- A `C³` scalar field has `C²` coordinate partial derivatives. -/
lemma contDiffAt_pd {n : ℕ} {f : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ} (μ : Fin n)
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
lemma pd_differentiableAt {n : ℕ} {f : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ} (μ : Fin n)
    (hf : ContDiffAt ℝ 2 f x) :
    DifferentiableAt ℝ (fun y => pd μ f y) x := by
  have hf_nhds : ∀ᶠ y in nhds x, ContDiffAt ℝ 2 f y := hf.eventually (by simp)
  have hcongr : pd μ f =ᶠ[nhds x] fun y => fderiv ℝ f y (Pi.single μ 1) :=
    hf_nhds.mono fun y hy => pd_eq_fderiv (hy.differentiableAt (by norm_num))
  have hdf' : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  exact (hdf'.clm_apply (differentiableAt_const _)).congr_of_eventuallyEq hcongr

/-- A differentiable field on `ℝⁿ` has differentiable coordinate slices. -/
lemma slice_differentiableAt {n : ℕ} {f : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ} (μ : Fin n)
    (hf : DifferentiableAt ℝ f x) :
    DifferentiableAt ℝ (fun s => f (Function.update x μ s)) (x μ) := by
  have hupd : (fun s : ℝ => Function.update x μ s)
      = fun s => x + (s - x μ) • (Pi.single μ 1 : Fin n → ℝ) := by
    ext s k; by_cases hk : k = μ <;> simp [Function.update, hk]
  have hd : HasDerivAt (fun s : ℝ => Function.update x μ s) (Pi.single μ (1 : ℝ)) (x μ) := by
    rw [hupd]
    simpa using (((hasDerivAt_id (x μ)).sub_const (x μ)).smul_const
      (Pi.single μ (1 : ℝ))).const_add x
  have hf' : HasFDerivAt f (fderiv ℝ f x) (Function.update x μ (x μ)) := by
    simpa [Function.update_eq_self] using hf.hasFDerivAt
  exact (hf'.comp_hasDerivAt (x μ) hd).differentiableAt

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

/-- Alias for the Minkowski metric field in inertial coordinates. -/
noncomputable abbrev minkowskiG : (Fin 4 → ℝ) → Tensor2 4 := GeneralRelativity.minkowskiG

/-!

## C. Flatness of constant metrics

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

end Pipeline

/-- Christoffel symbols of a `CoordinateMetric`. -/
noncomputable def CoordinateMetric.christoffel {n : ℕ} (C : CoordinateMetric n)
    (x : Fin n → ℝ) (k i j : Fin n) : ℝ :=
  Pipeline.christoffel C.g C.ginv x k i j

/-- Riemann curvature tensor of a `CoordinateMetric`. -/
noncomputable def CoordinateMetric.riemann {n : ℕ} (C : CoordinateMetric n)
    (x : Fin n → ℝ) (ρ σ μ ν : Fin n) : ℝ :=
  Pipeline.riemann C.g C.ginv x ρ σ μ ν

/-- Ricci tensor of a `CoordinateMetric`. -/
noncomputable def CoordinateMetric.ricciTensorOf {n : ℕ} (C : CoordinateMetric n)
    (x : Fin n → ℝ) (σ ν : Fin n) : ℝ :=
  Pipeline.ricciTensorOf C.g C.ginv x σ ν

/-- Scalar curvature of a `CoordinateMetric`. -/
noncomputable def CoordinateMetric.ricciScalarOf {n : ℕ} (C : CoordinateMetric n)
    (x : Fin n → ℝ) : ℝ :=
  Pipeline.ricciScalarOf C.g C.ginv x

/-- Einstein tensor of a `CoordinateMetric`. -/
noncomputable def CoordinateMetric.einsteinTensorOf {n : ℕ} (C : CoordinateMetric n)
    (x : Fin n → ℝ) (i j : Fin n) : ℝ :=
  Pipeline.einsteinTensorOf C.g C.ginv x i j

end GeneralRelativity
