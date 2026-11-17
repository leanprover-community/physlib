/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ClassicalFieldTheory.KleinGordon.Covariance.Operators

/-!

# The solution space as a Poincaré representation

The space of homogeneous solutions with spacelike compact support carries an action of the
Poincaré group. The causal propagator is an equivariant isomorphism from the compact sources
modulo the equation of motion to this space.

## i. Overview

A homogeneous solution with spacelike compact support is mapped to another one by every Poincaré
transformation. The causal hull of a set is mapped to the causal hull of the image by every
transformation including time reversals. The action on compact sources descends to the quotient by
the image of the equation of motion because the equation of motion is covariant. The isomorphism
of the quotient with the solution space sends the class of a source `f` to the causal propagator
`E f`. It is covariant for orthochronous transformations and changes sign for time reversals.

## ii. Key results

- `actSol` : the action on spacelike compact homogeneous solutions.
- `actQuot` : the action on compact sources modulo the equation of motion.
- `propagatorClass_actQuot` : the isomorphism is covariant for orthochronous transformations.
- `propagatorClass_actQuot_of_not` : the isomorphism changes sign under time reversals.

## iii. Table of contents

- A. The action on solutions
- B. The action on the quotient
- C. Covariance of the isomorphism

## iv. References

None.

## A. The action on solutions

- `actSol` : the action on spacelike compact homogeneous solutions.

## B. The action on the quotient

- `actQuot` : the action on compact sources modulo the equation of motion.

## C. Covariance of the isomorphism

- `propagatorClass_actQuot` : the isomorphism is covariant for orthochronous transformations.
-/

@[expose] public section

noncomputable section

open CausalRelation LocalOperator Minkowski KleinGordon.Spacetime PoincareGroup GreenOperator
open scoped Pointwise

namespace KleinGordon.Solution

variable {d : ℕ} {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F] {m : ℝ}

/-- Smooth fields form an additive group, needed to form the quotient. -/
local instance : AddCommGroup (smoothFields d F) := (smoothFields d F).addCommGroup

section Solutions

/-- The action preserves homogeneous solutions with spacelike compact support. -/
lemma actSmooth_mem_spacelikeCompactSolution (g : PoincareGroup d) {u : smoothFields d F}
    (hu : u ∈ (equation (d := d) (V := F) m).spacelikeCompactSolution (causalRelation d)) :
    actSmooth g u ∈ (equation (d := d) (V := F) m).spacelikeCompactSolution (causalRelation d) := by
  obtain ⟨hsc, hsol⟩ := Submodule.mem_inf.mp hu
  refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
  · obtain ⟨K, hK, hsub⟩ := hsc
    refine ⟨g • K, isCompact_smul g hK, ?_⟩
    rw [tsupport_actSmooth, causalHull_smul]
    exact Set.smul_set_mono hsub
  · have h0 : Spacetime.operator m u = 0 := hsol
    change Spacetime.operator m (actSmooth g u) = 0
    rw [operator_actSmooth, h0, map_zero]

/-- The action of the Poincaré group on homogeneous solutions with spacelike compact support. -/
def actSol (g : PoincareGroup d) :
    (equation (d := d) (V := F) m).spacelikeCompactSolution (causalRelation d) →ₗ[ℝ]
      (equation (d := d) (V := F) m).spacelikeCompactSolution (causalRelation d) :=
  (actSmooth g).restrict fun _ hu => actSmooth_mem_spacelikeCompactSolution g hu

/-- The value of a transformed solution. -/
@[simp]
lemma actSol_coe (g : PoincareGroup d)
    (u : (equation (d := d) (V := F) m).spacelikeCompactSolution (causalRelation d)) :
    ((actSol g u : (equation (d := d) (V := F) m).spacelikeCompactSolution (causalRelation d)) :
      smoothFields d F) = actSmooth g u := rfl

end Solutions

section Quotient

/-- Compact sources modulo the equation of motion. -/
abbrev SourceClasses (d : ℕ) (F : Type) [NormedAddCommGroup F] [NormedSpace ℂ F] (m : ℝ) :=
  (equation (d := d) (V := F) m).compactSources ⧸
    LinearMap.range (equation (d := d) (V := F) m).compactOperator

/-- The action on compact sources modulo the equation of motion. -/
def actQuot (g : PoincareGroup d) : SourceClasses d F m →ₗ[ℝ] SourceClasses d F m :=
  Submodule.mapQ _ _ (actTest g) (by
    rintro _ ⟨f, rfl⟩
    exact ⟨actTest g f, compactOperator_actTest m g f⟩)

/-- The action on the class of a source is the class of the transformed source. -/
@[simp]
lemma actQuot_mk (g : PoincareGroup d) (f : (equation (d := d) (V := F) m).compactSources) :
    actQuot (F := F) (m := m) g (Submodule.Quotient.mk f : SourceClasses d F m) =
      Submodule.Quotient.mk (actTest g f) := rfl

end Quotient

section Isomorphism

variable [CompleteSpace F]

/-- The isomorphism from the quotient of compact sources onto the solutions sends the class of a
source to its causal propagator. -/
lemma solutionsEquivQuotient_symm_mk (f : (equation (d := d) (V := F) m).compactSources) :
    ((solutionsEquivQuotient (d := d) (F := F) (m := m)).symm (Submodule.Quotient.mk f) :
        smoothFields d F) = propagator F m f := rfl

/-- The isomorphism of compact sources modulo the equation of motion with the solutions is
covariant under orthochronous Poincaré transformations. -/
lemma propagatorClass_actQuot {g : PoincareGroup d} (hg : g.IsOrthochronous)
    (x : SourceClasses d F m) :
    (solutionsEquivQuotient (d := d) (F := F) (m := m)).symm (actQuot (F := F) (m := m) g x) =
      actSol g ((solutionsEquivQuotient (d := d) (F := F) (m := m)).symm x) := by
  induction x using Submodule.Quotient.induction_on with
  | H f =>
    apply Subtype.ext
    rw [actQuot_mk, actSol_coe, solutionsEquivQuotient_symm_mk, solutionsEquivQuotient_symm_mk,
      propagator_actTest hg]

/-- The isomorphism changes sign under Poincaré transformations that reverse time. -/
lemma propagatorClass_actQuot_of_not {g : PoincareGroup d} (hg : ¬ g.IsOrthochronous)
    (x : SourceClasses d F m) :
    (solutionsEquivQuotient (d := d) (F := F) (m := m)).symm (actQuot (F := F) (m := m) g x) =
      -actSol g ((solutionsEquivQuotient (d := d) (F := F) (m := m)).symm x) := by
  induction x using Submodule.Quotient.induction_on with
  | H f =>
    apply Subtype.ext
    rw [actQuot_mk, Submodule.coe_neg, actSol_coe, solutionsEquivQuotient_symm_mk,
      solutionsEquivQuotient_symm_mk, propagator_actTest_of_not hg]

end Isomorphism

end KleinGordon.Solution
