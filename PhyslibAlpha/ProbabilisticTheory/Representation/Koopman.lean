/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ProbabilisticTheory.Representation.Commutant
public import PhyslibAlpha.ProbabilisticTheory.Representation.VectorMeasure
public import Mathlib.MeasureTheory.Function.L2Space

/-!

# The Koopman representation of a measure-preserving action

An abelian group acting on a probability space by measure-preserving maps acts unitarily on `L²`.

## i. Overview

Let an abelian group `G` act on a measurable space `X` by bijections preserving a measure `μ`, for
example lattice translations acting on the configurations of a classical spin system with a
translation-invariant ensemble `μ`. Then `(U_g f)(x) = f(g⁻¹ x)` is a unitary representation of `G`
on `L²(μ)`: the Koopman representation. The spectral theorem for unitary representations applies:
every `f ∈ L²(μ)`, an observable of the classical system, has a spectral measure `ν_f` on the
characters of `G` with `∫ χ(g) dν_f(χ) = ⟨f, U_g f⟩ = ∫ f̄(x) f(g⁻¹ x) dμ(x)`, the Fourier transform
of its correlation function. This is the structure factor of a classical lattice system. The
spectral projection of the trivial character projects onto the translation-invariant functions.
Nothing about quantum mechanics enters: this is the same representation theory that governs
quantum systems.

## ii. Key results

- `UnitaryRep.koopman` : the Koopman representation on `L²(μ)`.
- `UnitaryRep.koopman_apply_ae` : it acts by composition with the inverse group action.

## iii. Table of contents

- A. The Koopman operators
- B. The unitary representation
- C. Invariant functions

## iv. References

* None.

-/

@[expose] public section

noncomputable section

namespace ProbabilisticTheory

open MeasureTheory Set
open scoped ComplexOrder InnerProductSpace

namespace QuantumMechanics

namespace UnitaryRep

section Group

variable {Γ : Type*} [Group Γ]
variable {X : Type*} [MeasurableSpace X] (μ : Measure X)
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (T : Γ →* Equiv.Perm X) (hT : ∀ g, MeasurePreserving (T g) μ μ)

include hT

/-! ## A. The Koopman operators -/

/-- The composition operator `f ↦ f ∘ T_g⁻¹` on `L²(μ)` as a linear isometry. -/
def koopmanIsometry (g : Γ) : Lp E 2 μ →ₗᵢ[ℂ] Lp E 2 μ :=
  Lp.compMeasurePreservingₗᵢ ℂ (T g⁻¹) (hT g⁻¹)

omit hT [InnerProductSpace ℂ E] [CompleteSpace E] in
lemma compMeasurePreserving_congr {f f' : X → X} (hf : MeasurePreserving f μ μ)
    (hf' : MeasurePreserving f' μ μ) (e : f = f') (g : Lp E 2 μ) :
    Lp.compMeasurePreserving f hf g = Lp.compMeasurePreserving f' hf' g := by
  subst e; rfl

omit [CompleteSpace E] in
lemma koopmanIsometry_apply (g : Γ) (f : Lp E 2 μ) :
    koopmanIsometry μ T hT g f = Lp.compMeasurePreserving (T g⁻¹) (hT g⁻¹) f := rfl

omit [CompleteSpace E] in
lemma koopmanIsometry_mul (g h : Γ) (f : Lp E 2 μ) :
    koopmanIsometry μ T hT (g * h) f = koopmanIsometry μ T hT g (koopmanIsometry μ T hT h f) := by
  have hfun : (T (g * h)⁻¹ : X → X) = (T h⁻¹ : X → X) ∘ (T g⁻¹ : X → X) := by
    funext x
    rw [mul_inv_rev, map_mul]
    rfl
  have := Lp.compMeasurePreserving_comp_apply (E := E) (p := 2) f (hT h⁻¹) (hT g⁻¹)
  rw [koopmanIsometry_apply, koopmanIsometry_apply, koopmanIsometry_apply, ← this]
  exact compMeasurePreserving_congr μ _ _ hfun f

omit [CompleteSpace E] in
lemma koopmanIsometry_one (f : Lp E 2 μ) : koopmanIsometry μ T hT 1 f = f := by
  have hfun : (T (1 : Γ)⁻¹ : X → X) = id := by
    funext x; simp
  have := Lp.compMeasurePreserving_id_apply (E := E) (p := 2) (μb := μ) f
  rw [koopmanIsometry_apply]
  exact (compMeasurePreserving_congr μ _ (MeasurePreserving.id μ) hfun f).trans this

/-! ## B. The unitary representation -/

/-- The Koopman operator as a linear isometric equivalence. -/
def koopmanEquiv (g : Γ) : Lp E 2 μ ≃ₗᵢ[ℂ] Lp E 2 μ where
  toLinearEquiv := LinearEquiv.ofLinearMap (koopmanIsometry μ T hT g).toLinearMap
    (koopmanIsometry μ T hT g⁻¹).toLinearMap
    (LinearMap.ext fun f => by
      change koopmanIsometry μ T hT g (koopmanIsometry μ T hT g⁻¹ f) = f
      rw [← koopmanIsometry_mul, mul_inv_cancel, koopmanIsometry_one])
    (LinearMap.ext fun f => by
      change koopmanIsometry μ T hT g⁻¹ (koopmanIsometry μ T hT g f) = f
      rw [← koopmanIsometry_mul, inv_mul_cancel, koopmanIsometry_one])
  norm_map' := (koopmanIsometry μ T hT g).norm_map

omit [CompleteSpace E] in
lemma koopmanEquiv_one : koopmanEquiv (E := E) μ T hT 1 = 1 :=
  LinearIsometryEquiv.ext fun f => koopmanIsometry_one μ T hT f

omit [CompleteSpace E] in
lemma koopmanEquiv_mul (g h : Γ) :
    koopmanEquiv (E := E) μ T hT (g * h) =
      koopmanEquiv (E := E) μ T hT g * koopmanEquiv (E := E) μ T hT h :=
  LinearIsometryEquiv.ext fun f => koopmanIsometry_mul μ T hT g h f

/-- **The Koopman representation**: a group acting on a measure space by measure-preserving
bijections acts unitarily on `L²(μ)` by `(U_g f)(x) = f(g⁻¹ x)`. -/
def koopman : Γ →* unitary (Lp E 2 μ →L[ℂ] Lp E 2 μ) where
  toFun g := Unitary.linearIsometryEquiv.symm (koopmanEquiv μ T hT g)
  map_one' := by rw [koopmanEquiv_one, map_one]
  map_mul' g h := by rw [koopmanEquiv_mul, map_mul]

/-- The Koopman operator acts by composition with the inverse of the group action. -/
lemma koopman_apply (g : Γ) (f : Lp E 2 μ) :
    ((koopman μ T hT g : unitary (Lp E 2 μ →L[ℂ] Lp E 2 μ)) : Lp E 2 μ →L[ℂ] Lp E 2 μ) f =
      Lp.compMeasurePreserving (T g⁻¹) (hT g⁻¹) f := rfl

/-- **The correlation function of an observable**: the matrix coefficient of the Koopman
representation is the covariance `∫ ⟨f(x), f(g⁻¹ x)⟩ dμ(x)` of `f` with its translate. -/
lemma inner_koopman (g : Γ) (f : Lp E 2 μ) :
    ⟪f, ((koopman μ T hT g : unitary (Lp E 2 μ →L[ℂ] Lp E 2 μ)) : Lp E 2 μ →L[ℂ] Lp E 2 μ) f⟫_ℂ =
      ∫ x, ⟪f x, f (T g⁻¹ x)⟫_ℂ ∂μ := by
  rw [koopman_apply, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_compMeasurePreserving f (hT g⁻¹)] with x hx
  rw [hx]
  rfl

end Group

/-! ## C. Invariant functions -/

section Invariants

variable {G : Type*} [AddCommGroup G]
variable {X : Type*} [MeasurableSpace X] (μ : Measure X)
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (T : Multiplicative G →* Equiv.Perm X) (hT : ∀ g, MeasurePreserving (T g) μ μ)
variable [TopologicalSpace G] [DiscreteTopology G] [Countable G]
  [MeasurableSpace (PontryaginDual (Multiplicative G))]
  [BorelSpace (PontryaginDual (Multiplicative G))]

include hT in
/-- **Invariant observables of a classical system have zero momentum**: the spectral projection of
the trivial character of the Koopman representation projects onto the translation-invariant
functions in `L²(μ)`.   -/
lemma range_projection_one_koopman :
    LinearMap.range (projection (koopman (E := E) μ T hT)
        {(1 : PontryaginDual (Multiplicative G))} : Lp E 2 μ →L[ℂ] Lp E 2 μ).toLinearMap =
      ProbabilisticTheory.Representation.sector (toEnd (koopman (E := E) μ T hT)) (fun _ =>
        (1 : ℂ)) := by
  simpa using range_projection_singleton (koopman (E := E) μ T hT) (1 : PontryaginDual
    (Multiplicative G))

end Invariants

end UnitaryRep

end QuantumMechanics

end ProbabilisticTheory

end
