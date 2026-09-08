/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Michael Rothgang, Heather Macbeth, Matteo Cipollina
-/
module

public import Physlib.Mathematics.Geometry.Metric.PseudoRiemannian.Basic
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Metric

/-!
# Metric connections on pseudo-Riemannian vector bundles

This file is adapted from `Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Metric` by
Patrick Massot, Michael Rothgang and Heather Macbeth, whose statements and proofs it follows
line by line.

Mathlib's `CovariantDerivative.derivMetricTensor` and `IsMetricCompatible` are stated for bundles
whose fibres are `InnerProductSpace ℝ`. Positivity is used nowhere in them: the compatibility
tensor `(X, σ, τ) ↦ 𝓛_X g(σ, τ) - g(∇_X σ, τ) - g(σ, ∇_X τ)` needs only bilinearity, symmetry and
smoothness of the pairing. This file states them for `PseudoInnerProductSpace` fibres instead,
which is the generality the definitions actually have, and recovers Mathlib's Riemannian versions
as the special case (`derivMetricTensor_eq_derivPseudoMetricTensor`,
`isMetricCompatible_iff_isPseudoMetricCompatible`).

`CovariantDerivative` itself already assumes only that the fibres are topological vector spaces,
so nothing has to be generalized there; upstream, this file would replace
`Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Metric` rather than sit beside it.

## Main definitions

* `CovariantDerivative.derivPseudoMetricTensor`: the tensor
  `(X, σ, τ) ↦ 𝓛_X g(σ, τ) - g(∇_X σ, τ) - g(σ, ∇_X τ)`.
* `CovariantDerivative.IsPseudoMetricCompatible`: the connection is metric, i.e. that tensor
  vanishes.

## Main results

* `CovariantDerivative.isPseudoMetricCompatible_iff`: the pointwise Leibniz characterization.
* `CovariantDerivative.isMetricCompatible_iff_isPseudoMetricCompatible`: agreement with Mathlib's
  Riemannian notion.

## Tags

covariant derivative, connection, metric connection, pseudo-Riemannian, Levi-Civita
-/

@[expose] public section

open Bundle NormedSpace PseudoInnerProductSpace
open scoped Manifold ContDiff

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [∀ x, PseudoInnerProductSpace (V x)] [FiberBundle F V]

variable {σ σ' τ τ' : Π x : M, V x}

local notation "⟪" σ ", " τ "⟫" => fun x ↦ pseudoInner (σ x) (τ x)

namespace CovariantDerivative

variable (cov : CovariantDerivative I F V)

local syntax "∇" term:arg term : term
local macro_rules | `(∇ $X $σ) => `(fun (x : M) ↦ cov $σ x ($X x))

/-- The function defining the compatibility tensor for `∇` with respect to `g`; prefer
`derivPseudoMetricTensor`. -/
def derivPseudoMetricTensorAux (σ τ : Π x : M, V x) (x : M) : TangentSpace I x →L[ℝ] ℝ :=
  d% ⟪σ, τ⟫ x - flatL (V x) (τ x) ∘L cov σ x - flatL (V x) (σ x) ∘L cov τ x

@[simp]
lemma derivPseudoMetricTensorAux_apply (σ τ : Π x : M, V x) {x : M} (X₀ : TangentSpace I x) :
    derivPseudoMetricTensorAux I cov σ τ x X₀ =
      d% ⟪σ, τ⟫ x X₀ - pseudoInner (cov σ x X₀) (τ x) - pseudoInner (σ x) (cov τ x X₀) := by
  rw [pseudoInner_comm (cov σ x X₀) (τ x)]
  rfl

variable [VectorBundle ℝ F V] [IsContMDiffPseudoRiemannianBundle I 1 F V] {x : M}

theorem tensorial_derivPseudoMetricTensorAux₁ (τ : Π x, V x) (hτ : MDiffAt (T% τ) x) :
    TensorialAt I F (derivPseudoMetricTensorAux I cov · τ x) x where
  smul hf hσ := by
    ext X₀
    simp [mvfderiv_fun_mul hf (hσ.pseudoInner_bundle hτ),
      cov.isCovariantDerivativeOn.leibniz hσ hf, pseudoInner_add_left, pseudoInner_smul_left]
    ring
  add hσ hσ' := by
    ext X₀
    simp [mvfderiv_fun_add (hσ.pseudoInner_bundle hτ) (hσ'.pseudoInner_bundle hτ),
      cov.isCovariantDerivativeOn.add hσ hσ', pseudoInner_add_left]
    abel

theorem tensorial_derivPseudoMetricTensorAux₂ (σ : Π x, V x) (hσ : MDiffAt (T% σ) x) :
    TensorialAt I F (derivPseudoMetricTensorAux I cov σ · x) x where
  smul hf hτ := by
    ext X₀
    simp [mvfderiv_fun_mul hf (hσ.pseudoInner_bundle hτ),
      cov.isCovariantDerivativeOn.leibniz hτ hf, pseudoInner_add_right, pseudoInner_smul_right]
    ring
  add hτ hτ' := by
    ext X₀
    simp [mvfderiv_fun_add (hσ.pseudoInner_bundle hτ) (hσ.pseudoInner_bundle hτ'),
      cov.isCovariantDerivativeOn.add hτ hτ', pseudoInner_add_right]
    abel

variable {I} [ContMDiffVectorBundle 1 F V I] in
/-- The tensor `(X, σ, τ) ↦ X g(σ, τ) - g(∇_X σ, τ) - g(σ, ∇_X τ)` measuring the failure of `∇`
to be compatible with `g`. -/
def derivPseudoMetricTensor [FiniteDimensional ℝ F] (x : M) :
    V x →L[ℝ] V x →L[ℝ] (TangentSpace I x →L[ℝ] ℝ) :=
  TensorialAt.mkHom₂ (derivPseudoMetricTensorAux I cov · · x) _
    (tensorial_derivPseudoMetricTensorAux₁ I cov) (tensorial_derivPseudoMetricTensorAux₂ I cov)

variable {X : Π x : M, TangentSpace I x}

variable {I} [ContMDiffVectorBundle 1 F V I] in
theorem derivPseudoMetricTensor_apply [FiniteDimensional ℝ F] (x : M)
    (hσ : MDiffAt (T% σ) x) (hτ : MDiffAt (T% τ) x) :
    cov.derivPseudoMetricTensor x (σ x) (τ x) (X x) =
      d% ⟪σ, τ⟫ x (X x) - ⟪∇ X σ, τ⟫ x - ⟪σ, ∇ X τ⟫ x := by
  unfold derivPseudoMetricTensor
  rw [TensorialAt.mkHom₂_apply _ _ hσ hτ, derivPseudoMetricTensorAux_apply]

variable {I} [ContMDiffVectorBundle 1 F V I] in
theorem derivPseudoMetricTensor_apply_eq_extend [FiniteDimensional ℝ F]
    (X₀ : TangentSpace I x) (σ₀ τ₀ : V x) :
    cov.derivPseudoMetricTensor x σ₀ τ₀ X₀ =
      d% ⟪(FiberBundle.extend F σ₀), (FiberBundle.extend F τ₀)⟫ x X₀
        - pseudoInner (cov (FiberBundle.extend F σ₀) x X₀) τ₀
        - pseudoInner σ₀ (cov (FiberBundle.extend F τ₀) x X₀) := by
  simp [derivPseudoMetricTensor, TensorialAt.mkHom₂_apply_eq_extend]

set_option synthInstance.maxHeartbeats 100000 in
-- The `= 0` needs `Zero (Π x, V x →L[ℝ] V x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)`, which is over the
-- default budget: the fibres are topological vector spaces, so the strong topology on the
-- iterated hom-bundles is not the cheap normed-space instance the Riemannian case gets.
variable {I} [ContMDiffVectorBundle 1 F V I] in
/-- A connection is *metric* when it is compatible with the pseudo-inner product, i.e.
`X g(σ, τ) = g(∇_X σ, τ) + g(σ, ∇_X τ)`. -/
def IsPseudoMetricCompatible [FiniteDimensional ℝ F] : Prop := derivPseudoMetricTensor cov = 0

variable {I} [ContMDiffVectorBundle 1 F V I]

variable {cov} in
lemma IsPseudoMetricCompatible.mvfderiv_pseudoInner_eq [FiniteDimensional ℝ F]
    (hcov : cov.IsPseudoMetricCompatible) {x : M} (X : Π x, TangentSpace I x)
    {σ τ : (x : M) → V x} (hσ : MDiffAt (T% σ) x) (hτ : MDiffAt (T% τ) x) :
    d% ⟪σ, τ⟫ x (X x) = ⟪∇ X σ, τ⟫ x + ⟪σ, ∇ X τ⟫ x := by
  have H := congr($hcov x (σ x) (τ x) (X x))
  simp [derivPseudoMetricTensor_apply _ _ hσ hτ] at H
  linear_combination H

variable [IsManifold I 1 M]

lemma isPseudoMetricCompatible_iff [FiniteDimensional ℝ F] :
    cov.IsPseudoMetricCompatible ↔ ∀ {x : M} {X : Π x, TangentSpace I x} {σ τ : (x : M) → V x},
      MDiffAt (T% X) x → MDiffAt (T% σ) x → MDiffAt (T% τ) x →
      d% ⟪σ, τ⟫ x (X x) = ⟪∇ X σ, τ⟫ x + ⟪σ, ∇ X τ⟫ x := by
  refine ⟨fun hcov x X σ τ hX ↦ hcov.mvfderiv_pseudoInner_eq X, fun h ↦ ?_⟩
  ext1 x
  apply VectorBundle.injective_eval_mdifferentiableAt_sec I F V
    (V x →L[ℝ] (TangentSpace I x →L[ℝ] ℝ)) x
  ext1 σ; ext1 hσ
  apply VectorBundle.injective_eval_mdifferentiableAt_sec I F V
    (TangentSpace I x →L[ℝ] ℝ) x
  ext1 τ; ext1 hτ
  apply VectorBundle.injective_eval_mdifferentiableAt_sec I E (TangentSpace I); ext X hX
  simp (disch := assumption) [derivPseudoMetricTensor_apply]
  linear_combination h hX hσ hτ

/-! ## Agreement with Mathlib's Riemannian notion -/

section RiemannianBridge

variable
  {W : M → Type*} [TopologicalSpace (TotalSpace F W)]
  [∀ x, NormedAddCommGroup (W x)] [∀ x, InnerProductSpace ℝ (W x)]
  [FiberBundle F W] [VectorBundle ℝ F W] [IsContMDiffRiemannianBundle I 1 F W]
  [ContMDiffVectorBundle 1 F W I] [FiniteDimensional ℝ F]

omit [IsManifold I 1 M] in
/-- On a Riemannian bundle the pseudo-Riemannian compatibility tensor is Mathlib's: the
pseudo-inner product of the derived instance is the inner product. -/
lemma derivMetricTensor_eq_derivPseudoMetricTensor (cov : CovariantDerivative I F W) (x : M) :
    cov.derivMetricTensor x = cov.derivPseudoMetricTensor x := by
  ext σ₀ τ₀ X₀
  rw [derivMetricTensor_apply_eq_extend, derivPseudoMetricTensor_apply_eq_extend]
  rfl

/-- Mathlib's Riemannian notion of a metric connection is the special case of the
pseudo-Riemannian one. -/
lemma isMetricCompatible_iff_isPseudoMetricCompatible (cov : CovariantDerivative I F W) :
    cov.IsMetricCompatible ↔ cov.IsPseudoMetricCompatible := by
  rw [CovariantDerivative.isMetricCompatible_iff, isPseudoMetricCompatible_iff]
  exact Iff.rfl

end RiemannianBridge

end CovariantDerivative
