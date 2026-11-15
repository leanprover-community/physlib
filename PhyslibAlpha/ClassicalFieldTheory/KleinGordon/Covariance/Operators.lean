/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ClassicalFieldTheory.KleinGordon.Solution
public import PhyslibAlpha.ClassicalFieldTheory.WaveEquation.Poincare
public import PhyslibAlpha.Relativity.Poincare.Causality

/-!

# Poincaré covariance of the Klein–Gordon Green operators

The retarded and advanced solutions commute with the Poincaré group.

## i. Overview

The Klein–Gordon equation is invariant under the Poincaré group. If `u` solves the equation with
source `f` then `g • u` solves it with source `g • f`. An orthochronous element maps the causal
future of the support of `f` to the causal future of the support of `g • f`. So `g • R f` is a
solution with the support condition of the retarded solution for `g • f`. Uniqueness gives
`R (g • f) = g • R f`. The same holds for the advanced solution. An element that reverses time
exchanges the two. So the causal propagator `E` is covariant up to a sign.

## ii. Key results

- `operator_actSmooth` : the Klein–Gordon operator commutes with the Poincaré action.
- `retarded_actTest` : the retarded solution is covariant under orthochronous elements.
- `advanced_actTest` : the advanced solution is covariant under orthochronous elements.
- `retarded_actTest_of_not` : a time reversal exchanges retarded and advanced solutions.
- `propagator_actTest` : the causal propagator is covariant under orthochronous elements.

## iii. Table of contents

- A. The operator
- B. Uniqueness of advanced solutions
- C. Covariance of the Green operators
- D. Covariance of the causal propagator

## iv. References

None.

## A. The operator

- `operator_actSmooth` : the Klein–Gordon operator commutes with the Poincaré action.

## B. Uniqueness of advanced solutions

- `existsUnique_advanced` : a compact source has exactly one solution supported in the causal
  past of the source.

## C. Covariance of the Green operators

- `retarded_actTest` : the retarded solution is covariant under orthochronous elements.
- `advanced_actTest` : the advanced solution is covariant under orthochronous elements.
- `retarded_actTest_of_not` : a time reversal exchanges retarded and advanced solutions.
- `advanced_actTest_of_not` : the same for the advanced solution.

## D. Covariance of the causal propagator

- `propagator_actTest` : the causal propagator is covariant under orthochronous elements.
- `propagator_actTest_of_not` : a time reversal changes the sign of the causal propagator.
-/

@[expose] public section

noncomputable section

open CausalRelation LocalOperator Minkowski KleinGordon.Spacetime PoincareGroup GreenOperator
open scoped Pointwise

namespace KleinGordon.Solution

variable {d : ℕ}

section Operator

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The Klein–Gordon operator commutes with the action of the Poincaré group. -/
lemma operator_actSmooth (m : ℝ) (g : PoincareGroup d) (u : smoothFields d V) :
    Spacetime.operator m (actSmooth g u) = actSmooth g (Spacetime.operator m u) := by
  simp only [Spacetime.operator, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply,
    map_add,    map_smul, WaveEquation.smoothWaveOperator_actSmooth]

/-- The compact operator commutes with the action on test fields. -/
lemma compactOperator_actTest (m : ℝ) (g : PoincareGroup d) (f : TestField d V) :
    (equation m).compactOperator (actTest g f) = actTest g ((equation m).compactOperator f) :=
  Subtype.ext (operator_actSmooth m g f.1)

end Operator

section Uniqueness

variable (F : Type) [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F] (m : ℝ)

/-- A compact source has exactly one solution supported in the causal past of the source. -/
lemma existsUnique_advanced (f : TestField d F) :
    ∃! u : smoothFields d F, Spacetime.operator m u = f ∧
      tsupport (u : SpaceTime d → F) ⊆
        (causalRelation d).causalPast (tsupport (f : SpaceTime d → F)) :=
  (greenOperators F m).reverse.retarded.existsUnique_retardedSolution_of_localization
    (Minkowski.smoothFutureLocalization _) (hasCompactCausalDiamonds d).reverse f

end Uniqueness

section Covariance

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F] {m : ℝ}

omit [CompleteSpace F] in
/-- The support of a transformed test field is the image of the support. -/
lemma tsupport_actTest (g : PoincareGroup d) (f : TestField d F) :
    tsupport ((actTest g f : TestField d F) : SpaceTime d → F) =
      g • tsupport (f : SpaceTime d → F) :=
  tsupport_actSmooth g f.1

/-- The retarded solution is covariant under orthochronous Poincaré transformations. -/
lemma retarded_actTest {g : PoincareGroup d} (hg : g.IsOrthochronous) (f : TestField d F) :
    retarded F m (actTest g f) = actSmooth g (retarded F m f) := by
  refine (existsUnique_retarded (m := m) (actTest g f)).unique
    ⟨retarded_solves _, retarded_support _⟩ ⟨?_, ?_⟩
  · rw [operator_actSmooth, retarded_solves]; rfl
  · rw [tsupport_actSmooth, tsupport_actTest, causalFuture_smul hg]
    exact Set.smul_set_mono (retarded_support f)

/-- The advanced solution is covariant under orthochronous Poincaré transformations. -/
lemma advanced_actTest {g : PoincareGroup d} (hg : g.IsOrthochronous) (f : TestField d F) :
    advanced F m (actTest g f) = actSmooth g (advanced F m f) := by
  refine (existsUnique_advanced F m (actTest g f)).unique
    ⟨advanced_solves _, advanced_support _⟩ ⟨?_, ?_⟩
  · rw [operator_actSmooth, advanced_solves]; rfl
  · rw [tsupport_actSmooth, tsupport_actTest, causalPast_smul hg]
    exact Set.smul_set_mono (advanced_support f)

/-- A time reversal turns the retarded solution of the transformed source into the transformed
advanced solution. -/
lemma retarded_actTest_of_not {g : PoincareGroup d} (hg : ¬ g.IsOrthochronous)
    (f : TestField d F) : retarded F m (actTest g f) = actSmooth g (advanced F m f) := by
  refine (existsUnique_retarded (m := m) (actTest g f)).unique
    ⟨retarded_solves _, retarded_support _⟩ ⟨?_, ?_⟩
  · rw [operator_actSmooth, advanced_solves]; rfl
  · rw [tsupport_actSmooth, tsupport_actTest, causalFuture_smul_of_not hg]
    exact Set.smul_set_mono (advanced_support f)

/-- A time reversal turns the advanced solution of the transformed source into the transformed
retarded solution. -/
lemma advanced_actTest_of_not {g : PoincareGroup d} (hg : ¬ g.IsOrthochronous)
    (f : TestField d F) : advanced F m (actTest g f) = actSmooth g (retarded F m f) := by
  refine (existsUnique_advanced F m (actTest g f)).unique
    ⟨advanced_solves _, advanced_support _⟩ ⟨?_, ?_⟩
  · rw [operator_actSmooth, retarded_solves]; rfl
  · rw [tsupport_actSmooth, tsupport_actTest, causalPast_smul_of_not hg]
    exact Set.smul_set_mono (retarded_support f)

end Covariance

section Propagator

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F] {m : ℝ}

/-- The causal propagator is covariant under orthochronous Poincaré transformations. -/
lemma propagator_actTest {g : PoincareGroup d} (hg : g.IsOrthochronous) (f : TestField d F) :
    propagator F m (actTest g f) = actSmooth g (propagator F m f) := by
  rw [propagator_eq, propagator_eq, retarded_actTest hg, advanced_actTest hg, map_sub]

/-- A time reversal changes the sign of the causal propagator. -/
lemma propagator_actTest_of_not {g : PoincareGroup d} (hg : ¬ g.IsOrthochronous)
    (f : TestField d F) :
    propagator F m (actTest g f) = -actSmooth g (propagator F m f) := by
  rw [propagator_eq, propagator_eq, retarded_actTest_of_not hg, advanced_actTest_of_not hg,
    map_sub, neg_sub]

end Propagator

end KleinGordon.Solution
