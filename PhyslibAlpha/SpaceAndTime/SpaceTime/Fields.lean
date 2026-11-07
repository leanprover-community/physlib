/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.SpaceAndTime.SpaceTime.Derivatives
public import Mathlib.Analysis.Distribution.Distribution
public import PhyslibAlpha.Mathematics.Analysis.LocalOperator

/-!

# Smooth fields and distributions on spacetime

Smooth fields form a local space of functions on `SpaceTime d` with derivatives.

## i. Overview

Smooth fields form a local space of functions on `SpaceTime d` with derivatives. Distribution fields
are the distributions with values in a normed space.

## ii. Key results

- `smoothFields` : Smooth spacetime fields with values in a fixed real vector space.
- `TestField` : Smooth compactly supported test fields on Minkowski spacetime.
- `smoothDerivative` : The existing spacetime derivative restricted to smooth fields.
- `smoothFiberMap` : Apply a constant continuous linear transformation to each field value.
- `DistributionField` : Distributional fields on all of Minkowski spacetime use Mathlib's native
  continuous dual.
- `testFunctionEquiv` : The existing compact smooth test fields are Mathlib test functions on the
  whole spacetime.

## iii. Table of contents

- A. Smooth Minkowski fields
- B. Minkowski test fields and distributions

## iv. References

None.

## A. Smooth Minkowski fields

- `smoothFields` : Smooth spacetime fields with values in a fixed real vector space.
- `TestField` : Smooth compactly supported test fields on Minkowski spacetime.
- `smoothDerivative` : The existing spacetime derivative restricted to smooth fields.
- `smoothFiberMap` : Apply a constant continuous linear transformation to each field value.

Lemmas: `smoothFields_contDiff`, `smoothFields_isLocal`, `smoothDerivative_coe`,
`smoothDerivative_support`, `smoothField_support_sum`, `smoothFiberMap_derivative`.

## B. Minkowski test fields and distributions

- `DistributionField` : Distributional fields on all of Minkowski spacetime use Mathlib's native
  continuous dual.
- `testFunctionEquiv` : The existing compact smooth test fields are Mathlib test functions on the
  whole spacetime.

-/

@[expose] public section

noncomputable section

open scoped ContDiff
open SpaceTime minkowskiMatrix MeasureTheory

namespace Minkowski

section
variable {d : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Smooth spacetime fields with values in a fixed real vector space. -/
def smoothFields (d : ℕ) (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] :
    Submodule ℝ (SpaceTime d → V) where
  carrier := {u | ContDiff ℝ ∞ u}
  zero_mem' := by exact (contDiff_const : ContDiff ℝ ∞ (0 : SpaceTime d → V))
  add_mem' := by
    intro u v hu hv
    exact (show ContDiff ℝ ∞ u from hu).add (show ContDiff ℝ ∞ v from hv)
  smul_mem' := by
    intro a u hu
    exact (show ContDiff ℝ ∞ u from hu).const_smul a

/-- Smooth compactly supported test fields on Minkowski spacetime. -/
abbrev TestField (d : ℕ) (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] :=
  ↥(compactFields (smoothFields d V))

/-- The regularity carried by an admissible smooth field. -/
lemma smoothFields_contDiff (u : smoothFields d V) : ContDiff ℝ ∞ u.val := u.property

/-- Smooth spacetime fields satisfy the local gluing hypothesis of the Green extension theorem. -/
lemma smoothFields_isLocal : IsLocalFieldSpace (smoothFields d V) := by
  intro u hu
  change ContDiff ℝ ∞ u
  apply contDiff_iff_contDiffAt.mpr
  intro p
  obtain ⟨v, hv⟩ := hu p
  exact (smoothFields_contDiff v).contDiffAt.congr_of_eventuallyEq hv

/-- The existing spacetime derivative restricted to smooth fields. -/
def smoothDerivative (μ : Fin 1 ⊕ Fin d) : smoothFields d V →ₗ[ℝ] smoothFields d V where
  toFun u := ⟨SpaceTime.deriv μ u.val, by
    change ContDiff ℝ ∞ _
    exact SpaceTime.contDiff_deriv μ u.val (by simpa using smoothFields_contDiff u)⟩
  map_add' u v := Subtype.ext (SpaceTime.deriv_add μ u.val v.val
    ((smoothFields_contDiff u).differentiable (by simp)) ((smoothFields_contDiff v).differentiable
      (by simp)))
  map_smul' a u := Subtype.ext (SpaceTime.deriv_const_smul μ a
    ((smoothFields_contDiff u).differentiable (by simp)))

@[simp]
lemma smoothDerivative_coe (μ : Fin 1 ⊕ Fin d) (u : smoothFields d V) :
    (smoothDerivative μ u : SpaceTime d → V) = SpaceTime.deriv μ u.val := rfl

/-- Spacetime differentiation is local in the support sense required by field equations. -/
lemma smoothDerivative_support (μ : Fin 1 ⊕ Fin d) (u : smoothFields d V) :
    tsupport (smoothDerivative μ u : SpaceTime d → V) ⊆ tsupport (u : SpaceTime d → V) :=
  tsupport_fderiv_apply_subset ℝ (Lorentz.Vector.basis μ)

omit [NormedSpace ℝ V] in
lemma smoothField_support_sum {ι : Type*} (s : Finset ι)
    (f : ι → SpaceTime d → V) (K : Set (SpaceTime d))
    (hf : ∀ i ∈ s, tsupport (f i) ⊆ K) :
    tsupport (∑ i ∈ s, f i) ⊆ K := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (tsupport_add _ _).trans (Set.union_subset
      (hf a (Finset.mem_insert_self _ _))
      (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))))

/-- Apply a constant continuous linear transformation to each field value. -/
def smoothFiberMap {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (L : V →L[ℝ] W) : smoothFields d V →ₗ[ℝ] smoothFields d W where
  toFun u := ⟨fun p => L (u.val p), L.contDiff.comp (smoothFields_contDiff u)⟩
  map_add' _ _ := Subtype.ext (funext fun _ => L.map_add _ _)
  map_smul' _ _ := Subtype.ext (funext fun _ => L.map_smul _ _)

/-- Constant fibre transformations commute with spacetime differentiation. -/
lemma smoothFiberMap_derivative {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (L : V →L[ℝ] W) (μ : Fin 1 ⊕ Fin d) (u : smoothFields d V) :
    smoothDerivative μ (smoothFiberMap L u) = smoothFiberMap L (smoothDerivative μ u) := by
  apply Subtype.ext
  funext p
  change (fderiv ℝ (fun q => L (u.val q)) p) _ = L ((fderiv ℝ u.val p) _)
  have h := L.hasFDerivAt.comp p
    (((smoothFields_contDiff u).differentiable (by simp) p).hasFDerivAt)
  exact congrArg (fun D : SpaceTime d →L[ℝ] W => D (Lorentz.Vector.basis μ)) h.fderiv

/-- Distributional fields on all of Minkowski spacetime use Mathlib's native continuous dual. -/
abbrev DistributionField (d : ℕ) (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] :=
  Distribution (⊤ : TopologicalSpace.Opens (SpaceTime d)) V ⊤

/-- The existing compact smooth test fields are Mathlib test functions on the whole spacetime.
The equivalence is algebraic. The LF topology lives on the Mathlib side. -/
def testFunctionEquiv : TestField d V ≃ₗ[ℝ]
    _root_.TestFunction (⊤ : TopologicalSpace.Opens (SpaceTime d)) V ⊤ where
  toFun f := ⟨f.val.val, smoothFields_contDiff f.val, f.property, Set.subset_univ _⟩
  invFun φ := ⟨⟨φ, φ.contDiff⟩, φ.hasCompactSupport⟩
  left_inv f := by rfl
  right_inv φ := by rfl
  map_add' _ _ := by rfl
  map_smul' _ _ := by rfl
end

end Minkowski
