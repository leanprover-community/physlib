/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.Relativity.Poincare.Fields
public import PhyslibAlpha.Mathematics.Distribution.Translation
public import Mathlib.Analysis.Distribution.Support

/-!

# The Poincaré action on test functions and distributions

The Poincaré group acts on test functions by pullback and on distributions by transposition.

## i. Overview

A Poincaré element `g` acts on a test function by `(g • φ) x = φ (g⁻¹ x)`. The action is
continuous on the space of test functions because pullback by a Lorentz transformation and by a
translation are. A distribution `T` is transformed by `(g • T) φ = T (g⁻¹ • φ)`. Then the
delta distribution at `p` goes to the delta distribution at `g p`. A distribution that vanishes
outside a set goes to a distribution that vanishes outside the image of the set.

## ii. Key results

- `PoincareGroup.actTestFunction` : the action on test functions.
- `PoincareGroup.actDist` : the action on distributions.
- `PoincareGroup.isVanishingOn_actDist` : the support of a transformed distribution.
- `PoincareGroup.actDist_delta` : the action sends a delta distribution to a delta distribution.

## iii. Table of contents

- A. Test functions
- B. Distributions

## iv. References

None.

## A. Test functions

- `PoincareGroup.actTestFunction` : the action on test functions.

## B. Distributions

- `PoincareGroup.actDist` : the action on distributions.
-/

@[expose] public section

noncomputable section

open scoped Distributions ContDiff Pointwise
open TopologicalSpace Minkowski

namespace PoincareGroup

variable {d : ℕ}

/-- A Lorentz transformation as a continuous linear equivalence of spacetime. -/
def lorentzCLE (Λ : LorentzGroup d) : SpaceTime d ≃L[ℝ] SpaceTime d :=
  ContinuousLinearEquiv.equivOfInverse (Lorentz.Vector.actionCLM Λ) (Lorentz.Vector.actionCLM Λ⁻¹)
    (fun x => by simp [Lorentz.Vector.actionCLM_apply])
    (fun x => by simp [Lorentz.Vector.actionCLM_apply])

/-- The determinant of a Lorentz transformation has absolute value one. -/
lemma abs_det_lorentzCLE (Λ : LorentzGroup d) :
    |LinearMap.det (lorentzCLE Λ : SpaceTime d →ₗ[ℝ] SpaceTime d)| = 1 := by
  have h : LinearMap.toMatrix Lorentz.Vector.basis Lorentz.Vector.basis
      (lorentzCLE Λ : SpaceTime d →ₗ[ℝ] SpaceTime d) = Λ.1 := by
    ext i j
    rw [LinearMap.toMatrix_apply, Lorentz.Vector.basis_repr_apply]
    change (Λ • Lorentz.Vector.basis j) i = _
    rw [Lorentz.Vector.smul_eq_mulVec]
    simp [Matrix.mulVec, dotProduct, Lorentz.Vector.basis_apply]
  rw [← LinearMap.det_toMatrix Lorentz.Vector.basis, h]
  rcases LorentzGroup.det_eq_one_or_neg_one Λ with h | h <;> simp [h]

section TestFunctions

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The action of the Poincaré group on test functions. -/
def actTestFunction (g : PoincareGroup d) :
    𝓓((⊤ : Opens (SpaceTime d)), F) →L[ℝ] 𝓓((⊤ : Opens (SpaceTime d)), F) :=
  (TestFunction.precompLinearEquivCLM (lorentzCLE g⁻¹.lorentz)).comp
    (TestFunction.precompTranslationCLM g⁻¹.translation)

/-- The value of a transformed test function. -/
@[simp]
lemma actTestFunction_apply (g : PoincareGroup d) (φ : 𝓓((⊤ : Opens (SpaceTime d)), F))
    (x : SpaceTime d) : actTestFunction g φ x = φ (g⁻¹ • x) := rfl

/-- The inverse of a pure translation acts on test functions as the translate `x ↦ φ (x + p)`. -/
lemma actTestFunction_translation_inv (p : SpaceTime d) (φ : 𝓓((⊤ : Opens (SpaceTime d)), F)) :
    actTestFunction (⟨p, 1⟩ : PoincareGroup d)⁻¹ φ = TestFunction.precompTranslationCLM p φ := by
  ext x
  rw [actTestFunction_apply, inv_inv, smul_def, TestFunction.precompTranslationCLM_apply]
  change φ ((1 : LorentzGroup d) • x + p) = _
  rw [one_smul]

/-- The identity acts trivially on test functions. -/
lemma actTestFunction_one (φ : 𝓓((⊤ : Opens (SpaceTime d)), F)) :
    actTestFunction (1 : PoincareGroup d) φ = φ := by
  ext x
  simp

/-- The action on test functions is a left action. -/
lemma actTestFunction_mul (g h : PoincareGroup d) (φ : 𝓓((⊤ : Opens (SpaceTime d)), F)) :
    actTestFunction (g * h) φ = actTestFunction g (actTestFunction h φ) := by
  ext x
  simp [mul_smul]

/-- The support of a transformed test function is the image of the support. -/
lemma tsupport_actTestFunction (g : PoincareGroup d) (φ : 𝓓((⊤ : Opens (SpaceTime d)), F)) :
    tsupport (actTestFunction g φ) = g • tsupport φ :=
  tsupport_act g φ

end TestFunctions

section Distributions

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The action of the Poincaré group on distributions: `(g • T) φ = T (g⁻¹ • φ)`. -/
def actDist (g : PoincareGroup d) : DistributionField d V →L[ℝ] DistributionField d V :=
  (actTestFunction g⁻¹ : 𝓓((⊤ : Opens (SpaceTime d)), ℝ) →L[ℝ] _).precompCompactConvergenceCLM V

/-- The value of a transformed distribution. -/
lemma actDist_apply (g : PoincareGroup d) (T : DistributionField d V)
    (φ : 𝓓((⊤ : Opens (SpaceTime d)), ℝ)) : actDist g T φ = T (actTestFunction g⁻¹ φ) := rfl

/-- The identity acts trivially on distributions. -/
lemma actDist_one (T : DistributionField d V) : actDist (1 : PoincareGroup d) T = T := by
  ext φ
  simp [actDist_apply, actTestFunction_one]

/-- The action on distributions is a left action. -/
lemma actDist_mul (g h : PoincareGroup d) (T : DistributionField d V) :
    actDist (g * h) T = actDist g (actDist h T) := by
  ext φ
  simp [actDist_apply, actTestFunction_mul]

/-- A transformed distribution vanishes outside the image of the set. -/
lemma isVanishingOn_actDist (g : PoincareGroup d) {T : DistributionField d V}
    {U : Set (SpaceTime d)} (hT : Distribution.IsVanishingOn T U) :
    Distribution.IsVanishingOn (actDist g T) (g • U) := by
  intro φ hφ
  rw [actDist_apply]
  apply hT
  rw [tsupport_actTestFunction, ← Set.smul_set_subset_smul_set_iff (a := g)]
  simpa [smul_smul] using hφ

/-- The action sends a delta distribution to a delta distribution. -/
lemma actDist_delta (g : PoincareGroup d) (p : SpaceTime d) :
    actDist g (Distribution.delta p : DistributionField d ℝ) = Distribution.delta (g • p) := by
  ext φ
  simp [actDist_apply]

end Distributions

end PoincareGroup
