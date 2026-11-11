/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ClassicalFieldTheory.KleinGordon.Covariance.Operators
public import PhyslibAlpha.Relativity.Poincare.Distributions

/-!

# Poincaré covariance for distributional sources

The retarded and advanced solutions of compactly supported distributions are covariant.

## i. Overview

The Poincaré group acts on distributions by transposition. The Klein–Gordon operator on
distributions commutes with this action because the operator on test functions does. A
transformed compactly supported distribution is compactly supported. The transformed retarded
solution solves the equation for the transformed source and vanishes outside the transformed
causal future. Uniqueness of the retarded solution then gives covariance. The point source is a
retarded solution of a delta distribution. So it is covariant too.

## ii. Key results

- `testOperator_actTestFunction` : the operator on test functions is covariant.
- `distributionOperator_actDist` : the operator on distributions is covariant.
- `retardedDistribution_actCompact` : the retarded solution of a distribution is covariant.
- `retardedPointSource_actDist` : the retarded point source is covariant.

## iii. Table of contents

- A. The operator on test functions and distributions
- B. Compactly supported distributions
- C. Covariance of the solutions
- D. The point source

## iv. References

None.

## A. The operator on test functions and distributions

- `testOperator_actTestFunction` : the operator on test functions is covariant.
- `distributionOperator_actDist` : the operator on distributions is covariant.

## B. Compactly supported distributions

- `actCompact` : the action on compactly supported distributions.

## C. Covariance of the solutions

- `retardedDistribution_actCompact` : the retarded solution of a distribution is covariant.

## D. The point source

- `retardedPointSource_actDist` : the retarded point source is covariant.
-/

@[expose] public section

noncomputable section

open CausalRelation LocalOperator Minkowski KleinGordon.Spacetime PoincareGroup GreenOperator
  Distribution
open scoped Pointwise Distributions

namespace KleinGordon.Solution

variable {d : ℕ}

section Operator

/-- The action on test functions agrees with the action on test fields. -/
lemma actTestFunction_testFieldEquiv (g : PoincareGroup d) (f : TestField d ℝ) :
    actTestFunction g (testFieldEquiv ℝ f) = testFieldEquiv ℝ (actTest g f) := by
  ext x
  rfl

/-- The Klein–Gordon operator on test functions commutes with the Poincaré action. -/
lemma testOperator_actTestFunction (m : ℝ) (g : PoincareGroup d)
    (φ : 𝓓((⊤ : TopologicalSpace.Opens (SpaceTime d)), ℝ)) :
    Spacetime.testOperator m (actTestFunction g φ) =
      actTestFunction g (Spacetime.testOperator m φ) := by
  have hφ : φ = testFieldEquiv ℝ ((testFieldEquiv ℝ).symm φ) :=
    ((testFieldEquiv ℝ).apply_symm_apply φ).symm
  generalize (testFieldEquiv ℝ).symm φ = f at hφ
  subst hφ
  rw [actTestFunction_testFieldEquiv, nativeTestOperator_equiv, nativeTestOperator_equiv,
    actTestFunction_testFieldEquiv, compactOperator_actTest]

/-- The Klein–Gordon operator on distributions commutes with the Poincaré action. -/
lemma distributionOperator_actDist {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (m : ℝ) (g : PoincareGroup d) (T : DistributionField d V) :
    distributionOperator m (actDist g T) = actDist g (distributionOperator m T) := by
  ext φ
  rw [distributionOperator_apply, actDist_apply, actDist_apply, distributionOperator_apply,
    testOperator_actTestFunction]

end Operator

section Compact

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The action of the Poincaré group on compactly supported distributions. -/
def actCompact (g : PoincareGroup d) (T : compactDistributions (SpaceTime d) V) :
    compactDistributions (SpaceTime d) V :=
  ⟨actDist g T.1, g • (compactDistributionBound T : Set (SpaceTime d)),
    isCompact_smul g (compactDistributionBound T).isCompact, by
      rw [← Set.smul_set_compl]
      exact isVanishingOn_actDist g (compactDistributionBound_vanishes T)⟩

/-- The value of a transformed compactly supported distribution. -/
@[simp]
lemma actCompact_val (g : PoincareGroup d) (T : compactDistributions (SpaceTime d) V) :
    (actCompact g T : DistributionField d V) = actDist g T := rfl

variable {m : ℝ}

/-- The retarded solution of a distribution is covariant under orthochronous transformations. -/
lemma retardedDistribution_actCompact {g : PoincareGroup d} (hg : g.IsOrthochronous)
    (T : compactDistributions (SpaceTime d) V) :
    retardedDistribution m (actCompact g T) = actDist g (retardedDistribution m T) := by
  symm
  refine retardedDistribution_unique (actCompact g T) _
    (isCompact_smul g (compactDistributionBound T).isCompact) ?_ ?_
  · rw [causalFuture_smul hg, ← Set.smul_set_compl]
    exact isVanishingOn_actDist g (retardedDistribution_support T)
  · rw [distributionOperator_actDist, retardedDistribution_solves]
    rfl

/-- The advanced solution of a distribution is covariant under orthochronous transformations. -/
lemma advancedDistribution_actCompact {g : PoincareGroup d} (hg : g.IsOrthochronous)
    (T : compactDistributions (SpaceTime d) V) :
    advancedDistribution m (actCompact g T) = actDist g (advancedDistribution m T) := by
  symm
  refine advancedCompactResponse_unique m (actCompact g T) _ _
    (isCompact_smul g (compactDistributionBound T).isCompact) ?_ ?_
  · rw [causalPast_smul hg, ← Set.smul_set_compl]
    exact isVanishingOn_actDist g (advancedDistribution_support T)
  · rw [distributionOperator_actDist, advancedDistribution_solves]
    rfl

/-- A time reversal turns the retarded solution of the transformed source into the transformed
advanced solution. -/
lemma retardedDistribution_actCompact_of_not {g : PoincareGroup d} (hg : ¬ g.IsOrthochronous)
    (T : compactDistributions (SpaceTime d) V) :
    retardedDistribution m (actCompact g T) = actDist g (advancedDistribution m T) := by
  symm
  refine retardedDistribution_unique (actCompact g T) _
    (isCompact_smul g (compactDistributionBound T).isCompact) ?_ ?_
  · rw [causalFuture_smul_of_not hg, ← Set.smul_set_compl]
    exact isVanishingOn_actDist g (advancedDistribution_support T)
  · rw [distributionOperator_actDist, advancedDistribution_solves]
    rfl

/-- A time reversal turns the advanced solution of the transformed source into the transformed
retarded solution. -/
lemma advancedDistribution_actCompact_of_not {g : PoincareGroup d} (hg : ¬ g.IsOrthochronous)
    (T : compactDistributions (SpaceTime d) V) :
    advancedDistribution m (actCompact g T) = actDist g (retardedDistribution m T) := by
  symm
  refine advancedCompactResponse_unique m (actCompact g T) _ _
    (isCompact_smul g (compactDistributionBound T).isCompact) ?_ ?_
  · rw [causalPast_smul_of_not hg, ← Set.smul_set_compl]
    exact isVanishingOn_actDist g (retardedDistribution_support T)
  · rw [distributionOperator_actDist, retardedDistribution_solves]
    rfl

end Compact

section PointSource

/-- The delta distribution at `p` as a compactly supported distribution. -/
def deltaCompact (p : SpaceTime d) : compactDistributions (SpaceTime d) ℝ :=
  ⟨Distribution.delta p, {p}, isCompact_singleton, fun φ hφ => by
    change φ p = 0
    exact image_eq_zero_of_notMem_tsupport fun hp => hφ hp rfl⟩

/-- The action sends the delta distribution at `p` to the delta distribution at `g p`. -/
lemma actCompact_deltaCompact (g : PoincareGroup d) (p : SpaceTime d) :
    actCompact g (deltaCompact p) = deltaCompact (g • p) :=
  Subtype.ext (actDist_delta g p)

variable {m : ℝ}

/-- The retarded point source is the retarded solution of the delta distribution. -/
lemma retardedPointSource_eq (p : SpaceTime d) :
    retardedPointSource m p = retardedDistribution m (deltaCompact p) :=
  retardedDistribution_unique (deltaCompact p) _ isCompact_singleton (pointSource_support p)
    (pointSource_solves p)

/-- The advanced point source is the advanced solution of the delta distribution. -/
lemma advancedPointSource_eq (p : SpaceTime d) :
    advancedPointSource m p = advancedDistribution m (deltaCompact p) :=
  advancedCompactResponse_unique m (deltaCompact p) _ {p} isCompact_singleton
    (advancedPointSource_vanishes m p) (distributionOperator_advancedPointSource m p)

/-- The retarded point source is covariant under orthochronous transformations. -/
lemma retardedPointSource_actDist {g : PoincareGroup d} (hg : g.IsOrthochronous)
    (p : SpaceTime d) :
    actDist g (retardedPointSource m p) = retardedPointSource m (g • p) := by
  rw [retardedPointSource_eq, retardedPointSource_eq, ← retardedDistribution_actCompact hg,
    actCompact_deltaCompact]

/-- The advanced point source is covariant under orthochronous transformations. -/
lemma advancedPointSource_actDist {g : PoincareGroup d} (hg : g.IsOrthochronous)
    (p : SpaceTime d) :
    actDist g (advancedPointSource m p) = advancedPointSource m (g • p) := by
  rw [advancedPointSource_eq, advancedPointSource_eq, ← advancedDistribution_actCompact hg,
    actCompact_deltaCompact]

/-- A time reversal turns the transformed retarded point source into the advanced point
source at the transformed point. -/
lemma retardedPointSource_actDist_of_not {g : PoincareGroup d} (hg : ¬ g.IsOrthochronous)
    (p : SpaceTime d) :
    actDist g (retardedPointSource m p) = advancedPointSource m (g • p) := by
  rw [retardedPointSource_eq, advancedPointSource_eq, ← advancedDistribution_actCompact_of_not hg,
    actCompact_deltaCompact]

/-- A time reversal turns the transformed advanced point source into the retarded point source
at the transformed point. -/
lemma advancedPointSource_actDist_of_not {g : PoincareGroup d} (hg : ¬ g.IsOrthochronous)
    (p : SpaceTime d) :
    actDist g (advancedPointSource m p) = retardedPointSource m (g • p) := by
  rw [advancedPointSource_eq, retardedPointSource_eq, ← retardedDistribution_actCompact_of_not hg,
    actCompact_deltaCompact]

end PointSource

end KleinGordon.Solution
