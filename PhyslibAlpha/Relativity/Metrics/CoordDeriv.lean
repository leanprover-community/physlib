/-
Copyright (c) 2026 Alex Vergara Gil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Vergara Gil
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Physlib.SpaceAndTime.SpaceTime.Derivatives
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.Ring

/-!

# Coordinate partial derivatives

Coordinate-axis partial derivatives `coordDeriv μ f x` on `Fin n → ℝ`, algebraic and regularity
API, Schwarz mixed-derivative symmetry, and bridge to `SpaceTime.deriv`.

## i. Overview

On a coordinate chart `Fin n → ℝ`, `Pipeline.coordDeriv μ f x` differentiates the single-variable
slice `s ↦ f (Function.update x μ s)` at `x μ`. This module supplies linearity, neighborhood
congruence, `C²` differentiability, Schwarz symmetry (`coordDeriv_comm`), elementary trigonometric
slice derivatives, and the identification `coordDeriv_eq_spaceTime_deriv` with Physlib's
coordinate-free spacetime derivative `SpaceTime.deriv`.

## ii. Key results

- `Pipeline.coordDeriv` : coordinate partial derivative `∂_μ f(x)`.
- `Pipeline.coordDeriv_of_hasDerivAt`, `Pipeline.coordDeriv_const_slice`,
  `Pipeline.coordDeriv_const`, `Pipeline.coordDeriv_congr`,
  `Pipeline.coordDeriv_congr_nhds` : basic evaluation and congruence API.
- `Pipeline.coordDeriv_add`, `Pipeline.coordDeriv_sub`, `Pipeline.coordDeriv_const_mul`,
  `Pipeline.coordDeriv_sum` : linearity of coordinate partial derivatives.
- `Pipeline.coordDeriv_eq_fderiv`, `Pipeline.coordDeriv_eq_spaceTime_deriv` : Fréchet and
  `SpaceTime.deriv` bridges.
- `Pipeline.coordDeriv_comm`, `Pipeline.contDiffAt_coordDeriv`,
  `Pipeline.coordDeriv_differentiableAt` : Schwarz symmetry and `C²`/`C³` regularity.

## iii. Table of contents

- A. Coordinate partial derivatives and derivative API

## iv. References

* R. M. Wald, *General Relativity* (1984), Ch. 3 (Sec. 3.1). [ref: wald_1984_general_relativity]
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

## A. Coordinate partial derivatives and derivative API

Coordinate partial derivatives along basis axes `μ : Fin n` evaluate directional derivatives
`∂_μ f(x)` and preserve `C²` regularity and mixed-derivative symmetry.

-/

/-- Coordinate partial derivative of a `Real.sin · ^ 2` slice: `(sin² θ)' = 2 sin θ cos θ`. -/
lemma hasDerivAt_sin_sq (θ : ℝ) :
    HasDerivAt (fun t => Real.sin t ^ 2) (2 * Real.sin θ * Real.cos θ) θ :=
  ((hasDerivAt_pow 2 (Real.sin θ)).comp θ (Real.hasDerivAt_sin θ)).congr_deriv (by ring)

/-- Coordinate derivative of `cos² θ`: `(cos² θ)' = -2 cos θ sin θ`. -/
lemma hasDerivAt_cos_sq (θ : ℝ) :
    HasDerivAt (fun t => Real.cos t ^ 2) (-2 * Real.cos θ * Real.sin θ) θ :=
  ((hasDerivAt_pow 2 (Real.cos θ)).comp θ (Real.hasDerivAt_cos θ)).congr_deriv (by ring)

/-- The partial derivative of a scalar field along the coordinate `μ`: the derivative of
`s ↦ f (Function.update x μ s)` at `x μ`. -/
noncomputable def coordDeriv {n : ℕ} (μ : Fin n) (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : ℝ :=
  deriv (fun s : ℝ => f (Function.update x μ s)) (x μ)

/-- If the coordinate slice `s ↦ f (Function.update x μ s)` has derivative `d` at `x μ`, then
`coordDeriv μ f x = d`. -/
lemma coordDeriv_of_hasDerivAt {n : ℕ} (μ : Fin n) {f : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ} {d : ℝ}
    (h : HasDerivAt (fun s => f (Function.update x μ s)) d (x μ)) :
    coordDeriv μ f x = d :=
  h.deriv

/-- If the coordinate slice `s ↦ f (Function.update x μ s)` is constant, then `coordDeriv μ f x`
vanishes. -/
lemma coordDeriv_const_slice {n : ℕ} (μ : Fin n) {f : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ} (c : ℝ)
    (h : ∀ s, f (Function.update x μ s) = c) :
    coordDeriv μ f x = 0 := by
  simp [coordDeriv, funext h]

/-- The coordinate partial derivative of a constant field vanishes. -/
lemma coordDeriv_const {n : ℕ} (μ : Fin n) (c : ℝ) (x : Fin n → ℝ) :
    coordDeriv μ (fun _ => c) x = 0 := by
  simp [coordDeriv]

/-- `coordDeriv` depends only on the pointwise values of the field. -/
lemma coordDeriv_congr {n : ℕ} (μ : Fin n) {f g : (Fin n → ℝ) → ℝ} (x : Fin n → ℝ)
    (h : ∀ y, f y = g y) : coordDeriv μ f x = coordDeriv μ g x := by
  simp only [coordDeriv]
  exact congrArg (fun F => deriv F (x μ)) (funext fun s => h _)

/-- Agreement of partial derivatives for locally equal functions on a neighborhood of `x`. -/
lemma coordDeriv_congr_nhds {n : ℕ} (μ : Fin n) {f g : (Fin n → ℝ) → ℝ} (x : Fin n → ℝ)
    (hfg : f =ᶠ[nhds x] g) : coordDeriv μ f x = coordDeriv μ g x := by
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
lemma coordDeriv_eq_fderiv {n : ℕ} {f : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ} {μ : Fin n}
    (hf : DifferentiableAt ℝ f x) :
    coordDeriv μ f x = fderiv ℝ f x (Pi.single μ 1) := by
  have hupd : (fun s : ℝ => Function.update x μ s)
      = fun s => x + (s - x μ) • (Pi.single μ 1 : Fin n → ℝ) := by
    ext s k
    by_cases hk : k = μ <;> simp [Function.update, hk]
  have hd : HasDerivAt (fun s : ℝ => Function.update x μ s) (Pi.single μ (1 : ℝ)) (x μ) := by
    rw [hupd]
    have h1 : HasDerivAt (fun s : ℝ => s - x μ) 1 (x μ) := by
      simpa using (hasDerivAt_id (x μ)).sub_const (x μ)
    simpa using (h1.smul_const (Pi.single μ (1 : ℝ))).const_add x
  rw [coordDeriv]
  have hf' : HasFDerivAt f (fderiv ℝ f x) (Function.update x μ (x μ)) := by
    simpa [Function.update_eq_self] using hf.hasFDerivAt
  exact (hf'.comp_hasDerivAt (x μ) hd).deriv

/-- Coordinate partial derivatives on `Fin 4 → ℝ` agree with `Physlib`'s `SpaceTime.deriv` (`∂_`)
under the standard index equivalence `finSumFinEquiv : Fin 1 ⊕ Fin 3 ≃ Fin 4`. -/
lemma coordDeriv_eq_spaceTime_deriv {f : SpaceTime 3 → ℝ} (μ : Fin 1 ⊕ Fin 3) (y : SpaceTime 3)
    (hf : DifferentiableAt ℝ f y) :
    coordDeriv (finSumFinEquiv μ) (fun x : Fin 4 → ℝ => f (fun α => x (finSumFinEquiv α)))
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
    simp [L, Pi.single_apply, e.injective.eq_iff, eq_comm, Lorentz.Vector.basis_apply]
  have hx : L (fun k => y (e.symm k)) = y := by
    ext α; simp [L, e]
  have hcomp : HasFDerivAt (f ∘ L) ((fderiv ℝ f y).comp L) (fun k => y (e.symm k)) := by
    have hy : HasFDerivAt f (fderiv ℝ f y) (L (fun k => y (e.symm k))) := by
      rw [hx]; exact hf.hasFDerivAt
    exact hy.comp _ L.hasFDerivAt
  show coordDeriv (e μ) (f ∘ L) (fun k => y (e.symm k)) = SpaceTime.deriv μ f y
  rw [coordDeriv_eq_fderiv hcomp.differentiableAt, hcomp.fderiv,
    ContinuousLinearMap.comp_apply, hLsingle]
  rfl

/-- Schwarz symmetry of mixed second coordinate partial derivatives for `ContDiffAt ℝ 2`
fields. -/
lemma coordDeriv_comm {n : ℕ} {f : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ} (μ ν : Fin n)
    (hf : ContDiffAt ℝ 2 f x) :
    coordDeriv μ (coordDeriv ν f) x = coordDeriv ν (coordDeriv μ f) x := by
  have hf_nhds : ∀ᶠ y in nhds x, ContDiffAt ℝ 2 f y := hf.eventually (by simp)
  have hcongr1 : coordDeriv ν f =ᶠ[nhds x] fun y => fderiv ℝ f y (Pi.single ν 1) :=
    hf_nhds.mono fun y hy => coordDeriv_eq_fderiv (hy.differentiableAt (by norm_num))
  have hcongr2 : coordDeriv μ f =ᶠ[nhds x] fun y => fderiv ℝ f y (Pi.single μ 1) :=
    hf_nhds.mono fun y hy => coordDeriv_eq_fderiv (hy.differentiableAt (by norm_num))
  have hdf' : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hdiff1 : DifferentiableAt ℝ (fun y => fderiv ℝ f y (Pi.single ν 1)) x :=
    hdf'.clm_apply (differentiableAt_const _)
  have hdiff2 : DifferentiableAt ℝ (fun y => fderiv ℝ f y (Pi.single μ 1)) x :=
    hdf'.clm_apply (differentiableAt_const _)
  rw [coordDeriv_congr_nhds μ x hcongr1, coordDeriv_congr_nhds ν x hcongr2,
    coordDeriv_eq_fderiv hdiff1, coordDeriv_eq_fderiv hdiff2]
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

/-- Linearity of `coordDeriv` under pointwise addition of differentiable coordinate slices. -/
lemma coordDeriv_add {n : ℕ} (μ : Fin n) {f g : (Fin n → ℝ) → ℝ} (x : Fin n → ℝ)
    (hf : DifferentiableAt ℝ (fun s => f (Function.update x μ s)) (x μ))
    (hg : DifferentiableAt ℝ (fun s => g (Function.update x μ s)) (x μ)) :
    coordDeriv μ (fun y => f y + g y) x = coordDeriv μ f x + coordDeriv μ g x :=
  deriv_add hf hg

/-- Linearity of `coordDeriv` under pointwise subtraction of differentiable coordinate slices. -/
lemma coordDeriv_sub {n : ℕ} (μ : Fin n) {f g : (Fin n → ℝ) → ℝ} (x : Fin n → ℝ)
    (hf : DifferentiableAt ℝ (fun s => f (Function.update x μ s)) (x μ))
    (hg : DifferentiableAt ℝ (fun s => g (Function.update x μ s)) (x μ)) :
    coordDeriv μ (fun y => f y - g y) x = coordDeriv μ f x - coordDeriv μ g x :=
  deriv_sub hf hg

/-- Linearity of `coordDeriv` under constant scalar multiplication. -/
lemma coordDeriv_const_mul {n : ℕ} (μ : Fin n) (c : ℝ) {f : (Fin n → ℝ) → ℝ} (x : Fin n → ℝ) :
    coordDeriv μ (fun y => c * f y) x = c * coordDeriv μ f x := by
  simp only [coordDeriv]
  exact deriv_const_mul_field c

/-- Linearity of `coordDeriv` over finite `Fin m` sums of differentiable slices. -/
lemma coordDeriv_sum {n m : ℕ} (μ : Fin n) (F : Fin m → (Fin n → ℝ) → ℝ) (x : Fin n → ℝ)
    (hF : ∀ k, DifferentiableAt ℝ (fun s => F k (Function.update x μ s)) (x μ)) :
    coordDeriv μ (fun y => ∑ k : Fin m, F k y) x = ∑ k : Fin m, coordDeriv μ (F k) x := by
  have hs : (fun s => ∑ k : Fin m, F k (Function.update x μ s))
      = ∑ k : Fin m, fun s => F k (Function.update x μ s) := by
    funext s; simp only [Finset.sum_apply]
  simp only [coordDeriv, hs]
  exact deriv_sum fun k _ => hF k

/-- A `C³` scalar field has `C²` coordinate partial derivatives. -/
lemma contDiffAt_coordDeriv {n : ℕ} {f : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ} (μ : Fin n)
    (hf : ContDiffAt ℝ 3 f x) : ContDiffAt ℝ 2 (coordDeriv μ f) x := by
  have hf_nhds : ∀ᶠ y in nhds x, ContDiffAt ℝ 2 f y :=
    (hf.of_le (by norm_num)).eventually (by simp)
  have hcongr : coordDeriv μ f =ᶠ[nhds x] fun y => fderiv ℝ f y (Pi.single μ 1) :=
    hf_nhds.mono fun y hy => coordDeriv_eq_fderiv (hy.differentiableAt (by norm_num))
  have hdf' : ContDiffAt ℝ 2 (fderiv ℝ f) x := hf.fderiv_right (m := 2) (by norm_num)
  have hclm : ContDiffAt ℝ 2 (fun y => fderiv ℝ f y (Pi.single μ 1)) x :=
    hdf'.clm_apply contDiffAt_const
  exact hclm.congr_of_eventuallyEq hcongr

/-- A `C²` scalar field has differentiable coordinate partial derivatives. -/
lemma coordDeriv_differentiableAt {n : ℕ} {f : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ} (μ : Fin n)
    (hf : ContDiffAt ℝ 2 f x) :
    DifferentiableAt ℝ (fun y => coordDeriv μ f y) x := by
  have hf_nhds : ∀ᶠ y in nhds x, ContDiffAt ℝ 2 f y := hf.eventually (by simp)
  have hcongr : coordDeriv μ f =ᶠ[nhds x] fun y => fderiv ℝ f y (Pi.single μ 1) :=
    hf_nhds.mono fun y hy => coordDeriv_eq_fderiv (hy.differentiableAt (by norm_num))
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

end Pipeline

end GeneralRelativity
