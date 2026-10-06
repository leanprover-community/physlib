/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Mathlib.Analysis.Convex.Cone.Extension
public import Mathlib.Topology.ContinuousMap.Lattice
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
public import Mathlib.Topology.ContinuousMap.Ordered

/-!
# Positive functionals are integrals

A positive functional given on part of `C(X, ℝ)` is integration against a probability measure.

## i. Overview

On a compact space `X`, a positive linear functional on continuous functions is integration against
a measure. This is the Riesz–Markov–Kakutani theorem. Often the functional is only known on some
continuous functions, for example on observables seen as functions on the pure states.

Here the functional `φ` is given through a linear map `T : V → C(X, ℝ)` whose range contains the
constant `1`. Suppose `φ v ≥ 0` whenever `T v ≥ 0`, and `φ` equals `1` at a preimage of `1`. Then
`φ` is integration of `T` against a regular probability measure. The M. Riesz extension theorem
first extends `φ` positively to all continuous functions.

## ii. Key results

- `ContinuousMap.instPosSMulMono` proves that scaling by a nonnegative number preserves the order of
  continuous functions.
- `exists_positive_extension` proves that `φ` extends to a positive functional on `C(X, ℝ)`.
- `exists_regular_probabilityMeasure_integral_eq` proves that `φ` is an integral.

## iii. Table of contents

- A. Scaling continuous functions preserves their order
- B. Positive functionals are integrals

## iv. References

* None.

-/

@[expose] public section

open MeasureTheory

/-!

## A. Scaling continuous functions preserves their order

-/

instance ContinuousMap.instPosSMulMono {X : Type*} [TopologicalSpace X] :
    PosSMulMono ℝ C(X, ℝ) :=
  ⟨fun _ hc _ _ h x => mul_le_mul_of_nonneg_left (h x) hc⟩

/-!

## B. Positive functionals are integrals

-/

variable {X V : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [MeasurableSpace X]
  [BorelSpace X] [AddCommGroup V] [Module ℝ V] (T : V →ₗ[ℝ] C(X, ℝ)) (φ : V →ₗ[ℝ] ℝ)
  (hpos : ∀ v, 0 ≤ T v → 0 ≤ φ v)

omit [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X] in
include hpos in
lemma ker_le_ker_of_nonneg : LinearMap.ker T ≤ LinearMap.ker φ := fun v hv => by
  have h₁ := hpos v (by rw [LinearMap.mem_ker.1 hv])
  have h₂ := hpos (-v) (by rw [map_neg, LinearMap.mem_ker.1 hv, neg_zero])
  rw [map_neg, neg_nonneg] at h₂
  exact LinearMap.mem_ker.2 (le_antisymm h₂ h₁)

omit [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X] in
/-- The functional `φ` on the range of `T`. -/
noncomputable def rangeFunctional : C(X, ℝ) →ₗ.[ℝ] ℝ :=
  ⟨LinearMap.range T, (LinearMap.ker T).liftQ φ (ker_le_ker_of_nonneg T φ hpos) ∘ₗ
    T.quotKerEquivRange.symm.toLinearMap⟩

omit [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X] in
lemma rangeFunctional_apply (v : V) : rangeFunctional T φ hpos ⟨T v, v, rfl⟩ = φ v := by
  change (LinearMap.ker T).liftQ φ (ker_le_ker_of_nonneg T φ hpos)
    (T.quotKerEquivRange.symm ⟨T v, v, rfl⟩) = φ v
  rw [T.quotKerEquivRange.symm_apply_eq.2
    (Subtype.ext (LinearMap.quotKerEquivRange_apply_mk T v).symm)]
  rfl

variable {one : V} (hone : T one = 1)
include hpos hone

omit [T2Space X] [MeasurableSpace X] [BorelSpace X] in
/-- **M. Riesz extension**: `φ` extends to a positive functional on all continuous functions. -/
lemma exists_positive_extension : ∃ Λ : C(X, ℝ) →ₗ[ℝ] ℝ,
    (∀ v, Λ (T v) = φ v) ∧ ∀ g, 0 ≤ g → 0 ≤ Λ g := by
  obtain ⟨Λ, hΛ, hΛpos⟩ := riesz_extension (PointedCone.positive ℝ _) (rangeFunctional T φ hpos)
    (fun ⟨_, v, rfl⟩ hv => by rw [rangeFunctional_apply]; exact hpos v hv)
    fun g => ⟨⟨T (‖g‖ • one), _, rfl⟩, fun x => by
      simpa [hone, Real.norm_eq_abs, neg_le_iff_add_nonneg'] using
        (neg_abs_le (g x)).trans' (neg_le_neg (g.norm_coe_le_norm x))⟩
  exact ⟨Λ, fun v => (hΛ ⟨T v, v, rfl⟩).trans (rangeFunctional_apply T φ hpos v), hΛpos⟩

/-- **Positive functionals are integrals**: a positive linear functional through `T`, equal to `1`
on a preimage of `1`, is integration against a regular probability measure. -/
lemma exists_regular_probabilityMeasure_integral_eq (hφ : φ one = 1) :
    ∃ μ : Measure X, μ.Regular ∧ IsProbabilityMeasure μ ∧ ∀ v, ∫ x, T v x ∂μ = φ v := by
  obtain ⟨Λ, hΛ, hΛpos⟩ := exists_positive_extension T φ hpos hone
  let Λc : CompactlySupportedContinuousMap X ℝ →ₚ[ℝ] ℝ :=
    .mk₀ ⟨⟨fun g => Λ g.toContinuousMap, fun _ _ => map_add Λ _ _⟩, fun c _ => map_smul Λ c _⟩
      fun _ hg => hΛpos _ fun x => hg x
  have hint (g : C(X, ℝ)) : ∫ x, g x ∂RealRMK.rieszMeasure Λc = Λ g :=
    RealRMK.integral_rieszMeasure Λc (CompactlySupportedContinuousMap.continuousMapEquiv g)
  refine ⟨_, RealRMK.regular_rieszMeasure Λc, ⟨?_⟩, fun v => (hint (T v)).trans (hΛ v)⟩
  have := hint 1
  rw [← hone, hΛ, hφ, hone] at this
  simpa [measureReal_def] using congrArg ENNReal.ofReal this
