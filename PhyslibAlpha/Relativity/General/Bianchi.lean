/-
Copyright (c) 2026 The Gravitation formalisation contributors.
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
dimension `n : ℕ` for any smooth coordinate metric `(g, ginv)`.

## ii. Key results

* Schwarz symmetry of coordinate partial derivatives `pd_comm_of_contDiffAt`
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
* the general contracted Bianchi identity `contracted_bianchi`
  (`∇^μ Ric_{μλ} = ½ ∂_λ S`) and Einstein tensor conservation
  `covDiv_einstein_eq_zero` (`∇^μ G_{μλ} = 0`), together with their
  instantiation on any smooth `ChartSpacetime`.

## iii. Table of contents

- A. Partial-derivative calculus and Schwarz symmetry
- B. Covariant derivatives and divergence
- C. Metric compatibility and Riemann symmetries
- D. General Second Bianchi Identity
- E. General Contracted Bianchi Identity and Einstein Conservation
- F. ChartSpacetime instantiations

## iv. References

* S. M. Carroll, *Lecture Notes on General Relativity*, arXiv:gr-qc/9712019,
  §3.2, pp. 72–73. [ref: Carroll1997]
* J. Sbierski, *On the existence of a maximal Cauchy development for the
  Einstein equations — a dezornification*, arXiv:1309.7591, §2. [ref: sbierski_2013]

-/
@[expose] public section

namespace GeneralRelativity

/-! Compatibility names for the refactored core pipeline.  The local Bianchi
calculus below was written against the former `pd`, `ricciOf`, `scalarOf`, and
`einsteinOf` names; the upstream core now calls the same operations
`coordDeriv`, `ricciTensorOf`, `ricciScalarOf`, and `einsteinTensorOf`. -/
lemma pd_const {n : ℕ} (μ : Fin n) (c : ℝ) (x : Fin n → ℝ) :
    CoordinateCurvature.coordDeriv μ (fun _ => c) x = 0 :=
  CoordinateCurvature.coordDeriv_const μ c x

lemma pd_congr {n : ℕ} (μ : Fin n) {f g : (Fin n → ℝ) → ℝ} (x : Fin n → ℝ)
    (h : ∀ y, f y = g y) : CoordinateCurvature.coordDeriv μ f x = CoordinateCurvature.coordDeriv μ g x :=
  CoordinateCurvature.coordDeriv_congr μ x h

namespace Bianchi

open CoordinateCurvature Topology Filter

/-! ## A. Partial-derivative calculus and Schwarz symmetry -/

/-- The coordinate curve `s ↦ Function.update x μ s` has derivative
`Pi.single μ 1` at `x μ`. -/
lemma hasDerivAt_update {n : ℕ} (x : Fin n → ℝ) (μ : Fin n) :
    HasDerivAt (fun s : ℝ => Function.update x μ s) (Pi.single μ 1) (x μ) := by
  rw [hasDerivAt_pi]
  intro i
  by_cases h : i = μ
  · subst h
    have hfun : (fun s : ℝ => Function.update x i s i) = id := by
      funext s
      simp
    rw [hfun, Pi.single_eq_same]
    exact hasDerivAt_id (x i)
  · have hfun : (fun s : ℝ => Function.update x μ s i) = fun _ => x i := by
      funext s
      simp [Function.update_of_ne h]
    rw [hfun, Pi.single_eq_of_ne h]
    exact hasDerivAt_const (x μ) (x i)

/-- `CoordinateCurvature.coordDeriv` depends only on the germ of the field in a neighborhood of `x`. -/
lemma pd_congr_nhds {n : ℕ} (μ : Fin n) {f g : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ}
    (h : f =ᶠ[𝓝 x] g) : CoordinateCurvature.coordDeriv μ f x = CoordinateCurvature.coordDeriv μ g x := by
  have hcont : ContinuousAt (fun s : ℝ => Function.update x μ s) (x μ) :=
    (hasDerivAt_update x μ).continuousAt
  have heq : (fun s : ℝ => f (Function.update x μ s)) =ᶠ[𝓝 (x μ)]
      (fun s : ℝ => g (Function.update x μ s)) := by
    have h1 : Tendsto (fun s : ℝ => Function.update x μ s) (𝓝 (x μ)) (𝓝 x) := by
      simpa [Function.update_eq_self] using hcont.tendsto
    exact h1.eventually h
  exact heq.deriv_eq

/-- For a Fréchet-differentiable field, `CoordinateCurvature.coordDeriv μ f x` equals the directional
Fréchet derivative `fderiv ℝ f x (Pi.single μ 1)`. -/
lemma pd_eq_fderiv_single {n : ℕ} {f : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ}
    (hf : DifferentiableAt ℝ f x) (μ : Fin n) :
    CoordinateCurvature.coordDeriv μ f x = fderiv ℝ f x (Pi.single μ 1) := by
  have hu := hasDerivAt_update x μ
  have hfx : HasFDerivAt f (fderiv ℝ f x) (Function.update x μ (x μ)) := by
    simpa [Function.update_eq_self] using hf.hasFDerivAt
  exact (hfx.comp_hasDerivAt (x μ) hu).deriv

/-- Differentiability of a field at `x` implies differentiability along every
coordinate line through `x`. -/
lemma differentiableAt_line {n : ℕ} {f : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ}
    (hf : DifferentiableAt ℝ f x) (μ : Fin n) :
    DifferentiableAt ℝ (fun s : ℝ => f (Function.update x μ s)) (x μ) := by
  have hu := hasDerivAt_update x μ
  have hfx : HasFDerivAt f (fderiv ℝ f x) (Function.update x μ (x μ)) := by
    simpa [Function.update_eq_self] using hf.hasFDerivAt
  exact (hfx.comp_hasDerivAt (x μ) hu).differentiableAt

lemma pd_add {n : ℕ} (μ : Fin n) {f g : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    CoordinateCurvature.coordDeriv μ (fun y => f y + g y) x = CoordinateCurvature.coordDeriv μ f x + CoordinateCurvature.coordDeriv μ g x :=
  deriv_add (differentiableAt_line hf μ) (differentiableAt_line hg μ)

lemma pd_sub {n : ℕ} (μ : Fin n) {f g : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    CoordinateCurvature.coordDeriv μ (fun y => f y - g y) x = CoordinateCurvature.coordDeriv μ f x - CoordinateCurvature.coordDeriv μ g x :=
  deriv_sub (differentiableAt_line hf μ) (differentiableAt_line hg μ)

lemma pd_neg {n : ℕ} (μ : Fin n) (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) :
    CoordinateCurvature.coordDeriv μ (fun y => -f y) x = -CoordinateCurvature.coordDeriv μ f x := by
  simp [CoordinateCurvature.coordDeriv]

lemma pd_const_mul {n : ℕ} (μ : Fin n) (c : ℝ) {f : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ}
    (hf : DifferentiableAt ℝ f x) :
    CoordinateCurvature.coordDeriv μ (fun y => c * f y) x = c * CoordinateCurvature.coordDeriv μ f x :=
  deriv_const_mul c (differentiableAt_line hf μ)

lemma pd_mul {n : ℕ} (μ : Fin n) {f g : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    CoordinateCurvature.coordDeriv μ (fun y => f y * g y) x = CoordinateCurvature.coordDeriv μ f x * g x + f x * CoordinateCurvature.coordDeriv μ g x := by
  have hm := (differentiableAt_line hf μ).hasDerivAt.fun_mul
    (differentiableAt_line hg μ).hasDerivAt
  simpa [CoordinateCurvature.coordDeriv, Function.update_eq_self] using hm.deriv

lemma pd_sum {n : ℕ} {ι : Type*} (μ : Fin n) (s : Finset ι)
    (f : ι → (Fin n → ℝ) → ℝ) {x : Fin n → ℝ}
    (hf : ∀ i ∈ s, DifferentiableAt ℝ (f i) x) :
    CoordinateCurvature.coordDeriv μ (fun y => ∑ i ∈ s, f i y) x = ∑ i ∈ s, CoordinateCurvature.coordDeriv μ (f i) x := by
  have h := deriv_fun_sum (u := s)
    (A := fun i s' => f i (Function.update x μ s')) (x := x μ)
    (fun i hi => differentiableAt_line (hf i hi) μ)
  simpa [CoordinateCurvature.coordDeriv] using h

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
    exact pd_eq_fderiv_single hy ν
  exact hclm.congr_of_eventuallyEq heq

/-- **Schwarz's theorem for `CoordinateCurvature.coordDeriv`**: mixed second coordinate partial derivatives
of any `C²` field commute. -/
lemma pd_comm_of_contDiffAt {n : ℕ} {f : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ}
    (hf : ContDiffAt ℝ 2 f x) (μ ν : Fin n) :
    CoordinateCurvature.coordDeriv μ (CoordinateCurvature.coordDeriv ν f) x = CoordinateCurvature.coordDeriv ν (CoordinateCurvature.coordDeriv μ f) x := by
  have eval_eq : ∀ a b : Fin n,
      CoordinateCurvature.coordDeriv a (CoordinateCurvature.coordDeriv b f) x = fderiv ℝ (fderiv ℝ f) x (Pi.single a 1) (Pi.single b 1) := by
    intro a b
    let vb : Fin n → ℝ := Pi.single b (1 : ℝ)
    have heq : CoordinateCurvature.coordDeriv b f =ᶠ[𝓝 x] fun y => fderiv ℝ f y vb := by
      filter_upwards [eventually_differentiableAt_of_contDiffAt_two hf] with y hy
      exact pd_eq_fderiv_single hy b
    rw [pd_congr_nhds a heq]
    have hfd : DifferentiableAt ℝ (fderiv ℝ f) x :=
      (hf.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiableAt one_ne_zero
    have hc : HasFDerivAt (fun _ : Fin n → ℝ => vb) 0 x :=
      hasFDerivAt_const (𝕜 := ℝ) vb x
    have hclm := hfd.hasFDerivAt.clm_apply hc
    rw [pd_eq_fderiv_single hclm.differentiableAt a, hclm.fderiv]
    simp [vb]
  rw [eval_eq μ ν, eval_eq ν μ]
  exact hf.isSymmSndFDerivAt (by simp) (Pi.single μ 1) (Pi.single ν 1)

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
  have hsym : CoordinateCurvature.coordDeriv l (fun y => g y i j) x = CoordinateCurvature.coordDeriv l (fun y => g y j i) x :=
    pd_congr_nhds l (hgSymm.mono fun y hy => hy i j)
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
        (1 / 2) * (CoordinateCurvature.coordDeriv l (fun y => g y p q) x + CoordinateCurvature.coordDeriv p (fun y => g y l q) x
          - CoordinateCurvature.coordDeriv q (fun y => g y l p) x) := by
    intro p q
    simp only [christoffel, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    calc
      ∑ m, ∑ a, (1 / 2) * (ginv x a m *
          (CoordinateCurvature.coordDeriv l (fun y => g y p m) x + CoordinateCurvature.coordDeriv p (fun y => g y l m) x
            - CoordinateCurvature.coordDeriv m (fun y => g y l p) x)) * g x a q
          = ∑ m, (1 / 2) * (CoordinateCurvature.coordDeriv l (fun y => g y p m) x + CoordinateCurvature.coordDeriv p (fun y => g y l m) x
              - CoordinateCurvature.coordDeriv m (fun y => g y l p) x) * (∑ a, ginv x a m * g x a q) := by
            apply Finset.sum_congr rfl
            intro m _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro a _
            ring
      _ = ∑ m, (1 / 2) * (CoordinateCurvature.coordDeriv l (fun y => g y p m) x + CoordinateCurvature.coordDeriv p (fun y => g y l m) x
            - CoordinateCurvature.coordDeriv m (fun y => g y l p) x) * (if m = q then 1 else 0) := by
            apply Finset.sum_congr rfl
            intro m _
            rw [hInv m q]
      _ = (1 / 2) * (CoordinateCurvature.coordDeriv l (fun y => g y p q) x + CoordinateCurvature.coordDeriv p (fun y => g y l q) x
            - CoordinateCurvature.coordDeriv q (fun y => g y l p) x) := by
            simp
  have h1 := hsum i j
  have h2 : (∑ a, christoffel g ginv x a l j * g x i a) =
      (1 / 2) * (CoordinateCurvature.coordDeriv l (fun y => g y j i) x + CoordinateCurvature.coordDeriv j (fun y => g y l i) x
        - CoordinateCurvature.coordDeriv i (fun y => g y l j) x) := by
    have hg0 : ∀ a b, g x a b = g x b a := hgSymm.self_of_nhds
    have hrewrite : (∑ a, christoffel g ginv x a l j * g x i a) =
        ∑ a, christoffel g ginv x a l j * g x a i := by
      apply Finset.sum_congr rfl
      intro a _
      rw [hg0 i a]
    rw [hrewrite, hsum j i]
  have hpd_sym : CoordinateCurvature.coordDeriv l (fun y => g y j i) x = CoordinateCurvature.coordDeriv l (fun y => g y i j) x :=
    pd_congr_nhds l (hgSymm.mono fun y hy => hy j i)
  unfold covDeriv2
  rw [h1, h2, hpd_sym]
  ring

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
  have hdiff : ∀ j, ∑ k, (CoordinateCurvature.coordDeriv l (fun y => ginv y i k) x * g x k j
      + ginv x i k * CoordinateCurvature.coordDeriv l (fun y => g y k j) x) = 0 := by
    intro j
    have hconst : CoordinateCurvature.coordDeriv l (fun y => ∑ k, ginv y i k * g y k j) x = 0 := by
      rw [pd_congr_nhds l (hInvL.mono fun y hy => hy i j)]
      exact pd_const l _ x
    rw [pd_sum l Finset.univ (fun k y => ginv y i k * g y k j)
      (fun k _ => (hginvD i k).mul (hgD k j))] at hconst
    rw [← hconst]
    apply Finset.sum_congr rfl
    intro k _
    exact (pd_mul l (hginvD i k) (hgD k j)).symm
  have hpd_ginv : CoordinateCurvature.coordDeriv l (fun y => ginv y i b) x =
      -∑ j, ∑ k, ginv x i k * CoordinateCurvature.coordDeriv l (fun y => g y k j) x * ginv x j b := by
    have h1 : CoordinateCurvature.coordDeriv l (fun y => ginv y i b) x =
        ∑ k, CoordinateCurvature.coordDeriv l (fun y => ginv y i k) x * (∑ j, g x k j * ginv x j b) := by
      simp [hInvR]
    rw [h1]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    have hstep : ∀ j, (∑ k, CoordinateCurvature.coordDeriv l (fun y => ginv y i k) x * (g x k j * ginv x j b)) =
        -(∑ k, ginv x i k * CoordinateCurvature.coordDeriv l (fun y => g y k j) x * ginv x j b) := by
      intro j
      have hd := hdiff j
      have hmul : (∑ k, (CoordinateCurvature.coordDeriv l (fun y => ginv y i k) x * g x k j
          + ginv x i k * CoordinateCurvature.coordDeriv l (fun y => g y k j) x) * ginv x j b) = 0 := by
        rw [← Finset.sum_mul, hd, zero_mul]
      have hsplit : (∑ k, (CoordinateCurvature.coordDeriv l (fun y => ginv y i k) x * g x k j
          + ginv x i k * CoordinateCurvature.coordDeriv l (fun y => g y k j) x) * ginv x j b) =
          (∑ k, CoordinateCurvature.coordDeriv l (fun y => ginv y i k) x * (g x k j * ginv x j b))
            + ∑ k, ginv x i k * CoordinateCurvature.coordDeriv l (fun y => g y k j) x * ginv x j b := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro k _
        ring
      linarith
    simp_rw [hstep, Finset.sum_neg_distrib]
  have hmc : ∀ k j, CoordinateCurvature.coordDeriv l (fun y => g y k j) x =
      (∑ a, christoffel g ginv x a l k * g x a j)
        + ∑ a, christoffel g ginv x a l j * g x k a := by
    intro k j
    have h := metric_compat g ginv hgSymm hInvAt l k j
    unfold covDeriv2 at h
    linarith
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
  have hsplit : (∑ j, ∑ k, ginv x i k * CoordinateCurvature.coordDeriv l (fun y => g y k j) x * ginv x j b) =
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
  have hgD : ∀ i j, DifferentiableAt ℝ (fun y => g y i j) x :=
    fun i j => (hgC2 i j).differentiableAt two_ne_zero
  have hmc_nhds : ∀ a b c : Fin n,
      (fun y => CoordinateCurvature.coordDeriv c (fun z => g z a b) y) =ᶠ[𝓝 x]
        fun y => (∑ β, christoffel g ginv y β c a * g y β b)
          + ∑ β, christoffel g ginv y β c b * g y a β := by
    intro a b c
    have hS : ∀ᶠ y in 𝓝 x, ∀ᶠ z in 𝓝 y, ∀ i j, g z i j = g z j i :=
      eventually_eventually_nhds.mpr hgSymm
    filter_upwards [hS, hInv] with y hyS hyInv
    have h := metric_compat g ginv hyS hyInv c a b
    unfold covDeriv2 at h
    linarith
  have h2pd : ∀ p q : Fin n,
      CoordinateCurvature.coordDeriv p (CoordinateCurvature.coordDeriv q (fun z => g z α σ)) x =
        (∑ β, CoordinateCurvature.coordDeriv p (fun y => christoffel g ginv y β q α) x * g x β σ)
        + (∑ β, CoordinateCurvature.coordDeriv p (fun y => christoffel g ginv y β q σ) x * g x α β)
        + (∑ β, ∑ γ, christoffel g ginv x β q α * christoffel g ginv x γ p β * g x γ σ)
        + (∑ β, ∑ γ, christoffel g ginv x β q α * christoffel g ginv x γ p σ * g x β γ)
        + (∑ β, ∑ γ, christoffel g ginv x β q σ * christoffel g ginv x γ p α * g x γ β)
        + (∑ β, ∑ γ, christoffel g ginv x β q σ * christoffel g ginv x γ p β * g x α γ) := by
    intro p q
    rw [pd_congr_nhds p (hmc_nhds α σ q)]
    have h1 : DifferentiableAt ℝ (fun y => ∑ β, christoffel g ginv y β q α * g y β σ) x :=
      DifferentiableAt.fun_sum fun β _ => (hΓD β q α).mul (hgD β σ)
    have h2 : DifferentiableAt ℝ (fun y => ∑ β, christoffel g ginv y β q σ * g y α β) x :=
      DifferentiableAt.fun_sum fun β _ => (hΓD β q σ).mul (hgD α β)
    rw [pd_add p h1 h2,
      pd_sum p Finset.univ (fun β y => christoffel g ginv y β q α * g y β σ)
        (fun β _ => (hΓD β q α).fun_mul (hgD β σ)),
      pd_sum p Finset.univ (fun β y => christoffel g ginv y β q σ * g y α β)
        (fun β _ => (hΓD β q σ).fun_mul (hgD α β))]
    have hm1 : ∀ β, CoordinateCurvature.coordDeriv p (fun y => christoffel g ginv y β q α * g y β σ) x =
        CoordinateCurvature.coordDeriv p (fun y => christoffel g ginv y β q α) x * g x β σ +
          christoffel g ginv x β q α *
            ((∑ γ, christoffel g ginv x γ p β * g x γ σ) +
              ∑ γ, christoffel g ginv x γ p σ * g x β γ) := by
      intro β
      have hβ : CoordinateCurvature.coordDeriv p (fun y => g y β σ) x =
          (∑ γ, christoffel g ginv x γ p β * g x γ σ) +
            ∑ γ, christoffel g ginv x γ p σ * g x β γ := (hmc_nhds β σ p).self_of_nhds
      rw [pd_mul p (hΓD β q α) (hgD β σ), hβ]
    have hm2 : ∀ β, CoordinateCurvature.coordDeriv p (fun y => christoffel g ginv y β q σ * g y α β) x =
        CoordinateCurvature.coordDeriv p (fun y => christoffel g ginv y β q σ) x * g x α β +
          christoffel g ginv x β q σ *
            ((∑ γ, christoffel g ginv x γ p α * g x γ β) +
              ∑ γ, christoffel g ginv x γ p β * g x α γ) := by
      intro β
      have hβ : CoordinateCurvature.coordDeriv p (fun y => g y α β) x =
          (∑ γ, christoffel g ginv x γ p α * g x γ β) +
            ∑ γ, christoffel g ginv x γ p β * g x α γ := (hmc_nhds α β p).self_of_nhds
      rw [pd_mul p (hΓD β q σ) (hgD α β), hβ]
    simp_rw [hm1, hm2, mul_add, Finset.mul_sum, Finset.sum_add_distrib]
    simp_rw [mul_assoc]
    ring
  have hcomm : CoordinateCurvature.coordDeriv μ (CoordinateCurvature.coordDeriv ν (fun z => g z α σ)) x - CoordinateCurvature.coordDeriv ν (CoordinateCurvature.coordDeriv μ (fun z => g z α σ)) x = 0 := by
    rw [pd_comm_of_contDiffAt (hgC2 α σ) μ ν]
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
  rw [h2pd μ ν, h2pd ν μ, hcross1, hcross2, hswap1, hswap2, hswap3, hswap4] at hcomm
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
    exact pd_congr_nhds a (hΓ.mono fun y hy => hy k i j)
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
      DifferentiableAt ℝ (fun y => CoordinateCurvature.coordDeriv a (fun z => christoffel g ginv z k i j) y) x :=
    fun a k i j => (contDiffAt_one_pd (hΓC2 k i j) a).differentiableAt one_ne_zero
  have hpdR : ∀ a r s m p : Fin n,
      CoordinateCurvature.coordDeriv a (fun y => riemann g ginv y r s m p) x =
        CoordinateCurvature.coordDeriv a (fun y => CoordinateCurvature.coordDeriv m (fun z => christoffel g ginv z r p s) y) x
        - CoordinateCurvature.coordDeriv a (fun y => CoordinateCurvature.coordDeriv p (fun z => christoffel g ginv z r m s) y) x
        + ∑ c, (CoordinateCurvature.coordDeriv a (fun y => christoffel g ginv y r m c) x * christoffel g ginv x c p s
              + christoffel g ginv x r m c * CoordinateCurvature.coordDeriv a (fun y => christoffel g ginv y c p s) x
              - CoordinateCurvature.coordDeriv a (fun y => christoffel g ginv y r p c) x * christoffel g ginv x c m s
              - christoffel g ginv x r p c * CoordinateCurvature.coordDeriv a (fun y => christoffel g ginv y c m s) x) := by
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
    rw [pd_add a hsub hsum, pd_sub a (hdΓD m r p s) (hdΓD p r m s),
      pd_sum a Finset.univ
        (fun c y => christoffel g ginv y r m c * christoffel g ginv y c p s
          - christoffel g ginv y r p c * christoffel g ginv y c m s)
        (fun c _ => ((hΓD r m c).fun_mul (hΓD c p s)).fun_sub
          ((hΓD r p c).fun_mul (hΓD c m s)))]
    congr 1
    apply Finset.sum_congr rfl
    intro c _
    rw [pd_sub a ((hΓD r m c).fun_mul (hΓD c p s)) ((hΓD r p c).fun_mul (hΓD c m s)),
      pd_mul a (hΓD r m c) (hΓD c p s),
      pd_mul a (hΓD r p c) (hΓD c m s)]
    ring
  have halg := second_bianchi_of
    (fun k i j => christoffel g ginv x k i j)
    (fun a k i j => CoordinateCurvature.coordDeriv a (fun y => christoffel g ginv y k i j) x)
    (fun a b k i j => CoordinateCurvature.coordDeriv a (fun y => CoordinateCurvature.coordDeriv b (fun z => christoffel g ginv z k i j) y) x)
    (fun k i j => christoffel_symm g ginv hgSymm k i j)
    (fun a b k i j => pd_comm_of_contDiffAt (hΓC2 k i j) a b)
    l ρ σ μ ν
  rw [covDerivRiemann, covDerivRiemann, covDerivRiemann]
  rw [hpdR, hpdR, hpdR]
  simpa only [riemann] using halg

/-! ## E. General Contracted Bianchi Identity and Einstein Conservation -/

/-- Differentiability of `riemann` from `C²` Christoffel symbols. -/
lemma differentiableAt_riemann {n : ℕ} (g ginv : (Fin n → ℝ) → Tensor2 n) {x : Fin n → ℝ}
    (hΓC2 : ∀ k i j, ContDiffAt ℝ 2 (fun y => christoffel g ginv y k i j) x)
    (ρ σ μ ν : Fin n) :
    DifferentiableAt ℝ (fun y => riemann g ginv y ρ σ μ ν) x := by
  have hΓD : ∀ k i j, DifferentiableAt ℝ (fun y => christoffel g ginv y k i j) x :=
    fun k i j => (hΓC2 k i j).differentiableAt two_ne_zero
  have hdΓD : ∀ a k i j,
      DifferentiableAt ℝ (fun y => CoordinateCurvature.coordDeriv a (fun z => christoffel g ginv z k i j) y) x :=
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

/-- Contracting `ρ = μ` in `covDerivRiemann` yields `covDeriv2 (CoordinateCurvature.ricciTensor)`. -/
lemma sum_covDerivRiemann_ricci {n : ℕ} (g ginv : (Fin n → ℝ) → Tensor2 n) {x : Fin n → ℝ}
    (hΓC2 : ∀ k i j, ContDiffAt ℝ 2 (fun y => christoffel g ginv y k i j) x)
    (m σ l : Fin n) :
    (∑ r, covDerivRiemann g ginv x m r σ r l) =
      covDeriv2 g ginv (CoordinateCurvature.ricciTensor g ginv) x m σ l := by
  simp only [covDerivRiemann, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have hpd : (∑ r, CoordinateCurvature.coordDeriv m (fun y => riemann g ginv y r σ r l) x) =
      CoordinateCurvature.coordDeriv m (fun y => CoordinateCurvature.ricciTensor g ginv y σ l) x :=
    (pd_sum m Finset.univ (fun r y => riemann g ginv y r σ r l)
      (fun r _ => differentiableAt_riemann g ginv hΓC2 r σ r l)).symm
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
    covDiv2 g ginv (CoordinateCurvature.ricciTensor g ginv) x l = (1 / 2) * CoordinateCurvature.coordDeriv l (CoordinateCurvature.ricciScalar g ginv) x := by
  have hgD : ∀ i j, DifferentiableAt ℝ (fun y => g y i j) x :=
    fun i j => (hgC2 i j).differentiableAt two_ne_zero
  have hRD : ∀ ρ σ μ ν, DifferentiableAt ℝ (fun y => riemann g ginv y ρ σ μ ν) x :=
    fun ρ σ μ ν => differentiableAt_riemann g ginv hΓC2 ρ σ μ ν
  have hRicD : ∀ σ ν, DifferentiableAt ℝ (fun y => CoordinateCurvature.ricciTensor g ginv y σ ν) x :=
    fun σ ν => differentiableAt_ricciOf g ginv hΓC2 σ ν
  have hInvUp : ∀ a i j, CoordinateCurvature.coordDeriv a (fun y => ginv y i j) x =
      -(∑ c, christoffel g ginv x i a c * ginv x c j)
        - ∑ c, christoffel g ginv x j a c * ginv x i c := by
    intro a i j
    have h := inv_metric_compat g ginv hgSymm hInvL (hInvR.self_of_nhds)
      (hginvSymm.self_of_nhds) hgD hginvD a i j
    unfold covDeriv2Up at h
    linarith
  have hBsum :
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
  have hT1 :
      (∑ m, ∑ σ, ginv x m σ * ∑ r, covDerivRiemann g ginv x m r σ r l) =
        covDiv2 g ginv (CoordinateCurvature.ricciTensor g ginv) x l := by
    unfold covDiv2
    apply Finset.sum_congr rfl
    intro m _
    apply Finset.sum_congr rfl
    intro σ _
    rw [sum_covDerivRiemann_ricci g ginv hΓC2 m σ l]
  have hT3 :
      (∑ m, ∑ σ, ginv x m σ * ∑ r, covDerivRiemann g ginv x l r σ m r) =
        -CoordinateCurvature.coordDeriv l (CoordinateCurvature.ricciScalar g ginv) x := by
    have hpdS : CoordinateCurvature.coordDeriv l (CoordinateCurvature.ricciScalar g ginv) x =
        ∑ m, ∑ σ, (CoordinateCurvature.coordDeriv l (fun y => ginv y m σ) x * CoordinateCurvature.ricciTensor g ginv x m σ
          + ginv x m σ * CoordinateCurvature.coordDeriv l (fun y => CoordinateCurvature.ricciTensor g ginv y m σ) x) := by
      unfold CoordinateCurvature.ricciScalar
      rw [pd_sum l Finset.univ (fun m y => ∑ σ, ginv y m σ * CoordinateCurvature.ricciTensor g ginv y m σ)
        (fun m _ => DifferentiableAt.fun_sum fun σ _ => (hginvD m σ).fun_mul (hRicD m σ))]
      apply Finset.sum_congr rfl
      intro m _
      rw [pd_sum l Finset.univ (fun σ y => ginv y m σ * CoordinateCurvature.ricciTensor g ginv y m σ)
        (fun σ _ => (hginvD m σ).fun_mul (hRicD m σ))]
      apply Finset.sum_congr rfl
      intro σ _
      exact pd_mul l (hginvD m σ) (hRicD m σ)
    have hric_neg : ∀ m σ,
        (∑ r, covDerivRiemann g ginv x l r σ m r) =
          -covDeriv2 g ginv (CoordinateCurvature.ricciTensor g ginv) x l σ m := by
      intro m σ
      have hskew_cov : ∀ r, covDerivRiemann g ginv x l r σ m r =
          -covDerivRiemann g ginv x l r σ r m := by
        intro r
        have hpd_skew : CoordinateCurvature.coordDeriv l (fun y => riemann g ginv y r σ m r) x =
            -CoordinateCurvature.coordDeriv l (fun y => riemann g ginv y r σ r m) x := by
          rw [pd_congr l x (fun y => riemann_skew_last g ginv y r σ m r), pd_neg]
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
        (∑ m, ∑ σ, (CoordinateCurvature.coordDeriv l (fun y => ginv y m σ) x * CoordinateCurvature.ricciTensor g ginv x σ m
          + ginv x m σ * CoordinateCurvature.coordDeriv l (fun y => CoordinateCurvature.ricciTensor g ginv y σ m) x)) := by
      simp only [covDeriv2, mul_sub, Finset.sum_sub_distrib, hInvUp]
      have hA :
          (∑ m, ∑ σ, ginv x m σ * ∑ a, christoffel g ginv x a l σ * CoordinateCurvature.ricciTensor g ginv x a m) =
          (∑ m, ∑ σ, (∑ c, christoffel g ginv x σ l c * ginv x m c) * CoordinateCurvature.ricciTensor g ginv x σ m) := by
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
          (∑ m, ∑ σ, ginv x m σ * ∑ a, christoffel g ginv x a l m * CoordinateCurvature.ricciTensor g ginv x σ a) =
          (∑ m, ∑ σ, (∑ c, christoffel g ginv x m l c * ginv x c σ) * CoordinateCurvature.ricciTensor g ginv x σ m) := by
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
            - ∑ c, christoffel g ginv x σ l c * ginv x m c) * CoordinateCurvature.ricciTensor g ginv x σ m
            + ginv x m σ * CoordinateCurvature.coordDeriv l (fun y => CoordinateCurvature.ricciTensor g ginv y σ m) x)) =
          (∑ m, ∑ σ, ginv x m σ * CoordinateCurvature.coordDeriv l (fun y => CoordinateCurvature.ricciTensor g ginv y σ m) x)
            - (∑ m, ∑ σ, (∑ c, christoffel g ginv x σ l c * ginv x m c) * CoordinateCurvature.ricciTensor g ginv x σ m)
            - (∑ m, ∑ σ, (∑ c, christoffel g ginv x m l c * ginv x c σ) * CoordinateCurvature.ricciTensor g ginv x σ m) := by
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
    have hpd_g_sym : CoordinateCurvature.coordDeriv l (fun y => ginv y σ m) x = CoordinateCurvature.coordDeriv l (fun y => ginv y m σ) x :=
      pd_congr_nhds l (hginvSymm.mono fun y hy => hy σ m)
    rw [hpd_g_sym, hginv0 σ m]
  have hRcontract_nhds : ∀ r a : Fin n,
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
  have hT2 :
      (∑ m, ∑ σ, ginv x m σ * ∑ r, covDerivRiemann g ginv x r r σ l m) =
        covDiv2 g ginv (CoordinateCurvature.ricciTensor g ginv) x l := by
    have hginv0 : ∀ a b, ginv x a b = ginv x b a := hginvSymm.self_of_nhds
    have hstep : ∀ r,
        (∑ m, ∑ σ, ginv x m σ * covDerivRiemann g ginv x r r σ l m) =
          CoordinateCurvature.coordDeriv r (fun y => ∑ m, ∑ σ, ginv y m σ * riemann g ginv y r σ l m) x
          + ∑ a, christoffel g ginv x r r a *
              (∑ m, ∑ σ, ginv x m σ * riemann g ginv x a σ l m)
          - ∑ a, christoffel g ginv x a r l *
              (∑ m, ∑ σ, ginv x m σ * riemann g ginv x r σ a m) := by
      intro r
      have hpd_lhs :
          CoordinateCurvature.coordDeriv r (fun y => ∑ m, ∑ σ, ginv y m σ * riemann g ginv y r σ l m) x =
            ∑ m, ∑ σ, (CoordinateCurvature.coordDeriv r (fun y => ginv y m σ) x * riemann g ginv x r σ l m
              + ginv x m σ * CoordinateCurvature.coordDeriv r (fun y => riemann g ginv y r σ l m) x) := by
        rw [pd_sum r Finset.univ
          (fun m y => ∑ σ, ginv y m σ * riemann g ginv y r σ l m)
          (fun m _ => DifferentiableAt.fun_sum fun σ _ => (hginvD m σ).fun_mul (hRD r σ l m))]
        apply Finset.sum_congr rfl
        intro m _
        rw [pd_sum r Finset.univ
          (fun σ y => ginv y m σ * riemann g ginv y r σ l m)
          (fun σ _ => (hginvD m σ).fun_mul (hRD r σ l m))]
        apply Finset.sum_congr rfl
        intro σ _
        exact pd_mul r (hginvD m σ) (hRD r σ l m)
      have hsplit :
          (∑ m, ∑ σ, ((CoordinateCurvature.coordDeriv r (fun y => ginv y m σ) x) * riemann g ginv x r σ l m
            + ginv x m σ * CoordinateCurvature.coordDeriv r (fun y => riemann g ginv y r σ l m) x)) =
          (∑ m, ∑ σ, ginv x m σ * CoordinateCurvature.coordDeriv r (fun y => riemann g ginv y r σ l m) x)
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
                + ginv x m σ * CoordinateCurvature.coordDeriv r (fun y => riemann g ginv y r σ l m) x)) =
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
      rw [pd_congr_nhds r (hRcontract_nhds r l)]
      simp_rw [(hRcontract_nhds _ l).self_of_nhds, (hRcontract_nhds r _).self_of_nhds]
      rw [pd_sum r Finset.univ (fun m y => ginv y r m * CoordinateCurvature.ricciTensor g ginv y m l)
        (fun m _ => (hginvD r m).fun_mul (hRicD m l))]
      have hpm : ∀ m, CoordinateCurvature.coordDeriv r (fun y => ginv y r m * CoordinateCurvature.ricciTensor g ginv y m l) x =
          CoordinateCurvature.coordDeriv r (fun y => ginv y r m) x * CoordinateCurvature.ricciTensor g ginv x m l
            + ginv x r m * CoordinateCurvature.coordDeriv r (fun y => CoordinateCurvature.ricciTensor g ginv y m l) x :=
        fun m => pd_mul r (hginvD r m) (hRicD m l)
      simp_rw [hpm, hInvUp]
      simp only [covDeriv2, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
      have hX :
          (∑ a, christoffel g ginv x r r a * ∑ m, ginv x a m * CoordinateCurvature.ricciTensor g ginv x m l) =
          (∑ m, (∑ c, christoffel g ginv x r r c * ginv x c m) * CoordinateCurvature.ricciTensor g ginv x m l) := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro m _
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro c _
        ring
      have hY :
          (∑ m, ginv x r m * ∑ a, christoffel g ginv x a r m * CoordinateCurvature.ricciTensor g ginv x a l) =
          (∑ m, (∑ c, christoffel g ginv x m r c * ginv x r c) * CoordinateCurvature.ricciTensor g ginv x m l) := by
        simp_rw [Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro m _
        apply Finset.sum_congr rfl
        intro c _
        ring
      have hZ :
          (∑ a, christoffel g ginv x a r l * ∑ m, ginv x r m * CoordinateCurvature.ricciTensor g ginv x m a) =
          (∑ m, ginv x r m * ∑ a, christoffel g ginv x a r l * CoordinateCurvature.ricciTensor g ginv x m a) := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro m _
        apply Finset.sum_congr rfl
        intro a _
        ring
      have hsplit :
          (∑ m, (-(∑ c, christoffel g ginv x r r c * ginv x c m)
            - ∑ c, christoffel g ginv x m r c * ginv x r c) * CoordinateCurvature.ricciTensor g ginv x m l) =
          -(∑ m, (∑ c, christoffel g ginv x r r c * ginv x c m) * CoordinateCurvature.ricciTensor g ginv x m l)
            - (∑ m, (∑ c, christoffel g ginv x m r c * ginv x r c) * CoordinateCurvature.ricciTensor g ginv x m l) := by
        have hm : ∀ m,
            (-(∑ c, christoffel g ginv x r r c * ginv x c m)
              - ∑ c, christoffel g ginv x m r c * ginv x r c) * CoordinateCurvature.ricciTensor g ginv x m l =
            -((∑ c, christoffel g ginv x r r c * ginv x c m) * CoordinateCurvature.ricciTensor g ginv x m l)
              - (∑ c, christoffel g ginv x m r c * ginv x r c) * CoordinateCurvature.ricciTensor g ginv x m l := by
          intro m; ring
        simp_rw [hm, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
      rw [hsplit, hX, hY, hZ]
      ring
    simp_rw [hstep2]
    rfl
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
  have hRicD : ∀ σ ν, DifferentiableAt ℝ (fun y => CoordinateCurvature.ricciTensor g ginv y σ ν) x :=
    fun σ ν => differentiableAt_ricciOf g ginv hΓC2 σ ν
  have hSD : DifferentiableAt ℝ (CoordinateCurvature.ricciScalar g ginv) x :=
    differentiableAt_scalarOf g ginv hginvD hΓC2
  have hInvAt : ∀ m j, ∑ a, ginv x a m * g x a j = if m = j then 1 else 0 := by
    intro m j
    simpa [hginvSymm.self_of_nhds] using hInvL.self_of_nhds m j
  have hcd : ∀ μ ν,
      covDeriv2 g ginv (CoordinateCurvature.einsteinTensor g ginv) x μ ν l =
        covDeriv2 g ginv (CoordinateCurvature.ricciTensor g ginv) x μ ν l
          - (1 / 2) * CoordinateCurvature.coordDeriv μ (CoordinateCurvature.ricciScalar g ginv) x * g x ν l := by
    intro μ ν
    unfold covDeriv2 CoordinateCurvature.einsteinTensor
    have hsub := pd_sub μ (hRicD ν l) ((hSD.const_mul (1 / 2 : ℝ)).fun_mul (hgD ν l))
    have hmul := pd_mul μ (hSD.const_mul (1 / 2 : ℝ)) (hgD ν l)
    have hcmul := pd_const_mul μ (1 / 2 : ℝ) hSD
    have hmc := metric_compat g ginv hgSymm hInvAt μ ν l
    unfold covDeriv2 at hmc
    rw [hsub, hmul, hcmul]
    simp_rw [mul_sub, Finset.sum_sub_distrib]
    have h1 :
        (∑ a, christoffel g ginv x a μ ν * ((1 / 2) * CoordinateCurvature.ricciScalar g ginv x * g x a l)) =
        (1 / 2) * CoordinateCurvature.ricciScalar g ginv x * ∑ a, christoffel g ginv x a μ ν * g x a l := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      ring
    have h2 :
        (∑ a, christoffel g ginv x a μ l * ((1 / 2) * CoordinateCurvature.ricciScalar g ginv x * g x ν a)) =
        (1 / 2) * CoordinateCurvature.ricciScalar g ginv x * ∑ a, christoffel g ginv x a μ l * g x ν a := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      ring
    rw [h1, h2]
    linear_combination -((1 / 2) * CoordinateCurvature.ricciScalar g ginv x) * hmc
  have hdiv :
      covDiv2 g ginv (CoordinateCurvature.einsteinTensor g ginv) x l =
        covDiv2 g ginv (CoordinateCurvature.ricciTensor g ginv) x l
          - (1 / 2) * CoordinateCurvature.coordDeriv l (CoordinateCurvature.ricciScalar g ginv) x := by
    unfold covDiv2
    simp_rw [hcd, mul_sub, Finset.sum_sub_distrib]
    congr 1
    calc
      ∑ μ, ∑ ν, ginv x μ ν * ((1 / 2) * CoordinateCurvature.coordDeriv μ (CoordinateCurvature.ricciScalar g ginv) x * g x ν l)
          = ∑ μ, (1 / 2) * CoordinateCurvature.coordDeriv μ (CoordinateCurvature.ricciScalar g ginv) x * (∑ ν, ginv x μ ν * g x ν l) := by
            apply Finset.sum_congr rfl
            intro μ _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro ν _
            ring
      _ = (1 / 2) * CoordinateCurvature.coordDeriv l (CoordinateCurvature.ricciScalar g ginv) x := by
            simp_rw [hInvL.self_of_nhds]
            simp
  rw [hdiv, contracted_bianchi g ginv hgSymm hginvSymm hInvL hInvR hgC2 hginvD hΓC2 l]
  ring

/-! ## F. ChartSpacetime instantiations -/

/-- Any `ChartSpacetime` with `C²` Christoffel symbols satisfies the second
Bianchi identity everywhere in the chart. -/
lemma chartSpacetime_second_bianchi (X : ChartSpacetime) {x : SpacetimeChart}
    (hΓC2 : ∀ k i j, ContDiffAt ℝ 2 (fun y => X.christoffel y k i j) x)
    (l ρ σ μ ν : Fin 4) :
    covDerivRiemann X.coordinateMetric X.coordinateInverseMetric x l ρ σ μ ν
      + covDerivRiemann X.coordinateMetric X.coordinateInverseMetric x μ ρ σ ν l
      + covDerivRiemann X.coordinateMetric X.coordinateInverseMetric x ν ρ σ l μ = 0 :=
  second_bianchi X.coordinateMetric X.coordinateInverseMetric
    (Filter.Eventually.of_forall fun y i j => (X.metric (X.chart.symm y)).symm.apply j i)
    hΓC2 l ρ σ μ ν

/-- Any `ChartSpacetime` with `C²` metric, differentiable inverse metric, and
`C²` Christoffel symbols satisfies the contracted Bianchi identity and Einstein
tensor conservation `∇^μ G_{μl} = 0`. -/
lemma chartSpacetime_covDiv_einstein_eq_zero (X : ChartSpacetime) {x : SpacetimeChart}
    (hgC2 : ∀ i j, ContDiffAt ℝ 2 (fun y => X.coordinateMetric y i j) x)
    (hginvD : ∀ i j, DifferentiableAt ℝ (fun y => X.coordinateInverseMetric y i j) x)
    (hΓC2 : ∀ k i j, ContDiffAt ℝ 2 (fun y => X.christoffel y k i j) x)
    (l : Fin 4) :
    covDiv2 X.coordinateMetric X.coordinateInverseMetric X.einstein x l = 0 := by
  have hInvL : ∀ y i j,
      ∑ k, X.coordinateInverseMetric y i k * X.coordinateMetric y k j =
        if i = j then 1 else 0 := by
    intro y i j
    have h := congrFun (congrFun (X.metric (X.chart.symm y)).inv_right i) j
    simpa [ChartSpacetime.coordinateMetric, ChartSpacetime.coordinateInverseMetric,
      Matrix.mul_apply, Matrix.one_apply] using h
  have hInvR : ∀ y i j,
      ∑ k, X.coordinateMetric y i k * X.coordinateInverseMetric y k j =
        if i = j then 1 else 0 := by
    intro y i j
    have h := congrFun (congrFun (X.metric (X.chart.symm y)).inv_left i) j
    simpa [ChartSpacetime.coordinateMetric, ChartSpacetime.coordinateInverseMetric,
      Matrix.mul_apply, Matrix.one_apply] using h
  exact covDiv_einstein_eq_zero X.coordinateMetric X.coordinateInverseMetric
    (Filter.Eventually.of_forall fun y i j => (X.metric (X.chart.symm y)).symm.apply j i)
    (Filter.Eventually.of_forall fun y i j => (X.metric (X.chart.symm y)).ginv_symm.apply j i)
    (Filter.Eventually.of_forall hInvL)
    (Filter.Eventually.of_forall hInvR)
    hgC2 hginvD hΓC2 l

end Bianchi

end GeneralRelativity
