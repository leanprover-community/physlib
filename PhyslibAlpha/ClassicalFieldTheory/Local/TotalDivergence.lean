/-
Copyright (c) 2026 Juan Jose Fernandez Morales. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Jose Fernandez Morales
-/
module

public import PhyslibAlpha.ClassicalFieldTheory.Local.FirstOrder
/-!
# Total divergences in local classical field theory

Packaged total-divergence Lagrangians and the Euler-Lagrange-triviality property.

## i. Overview

This module introduces the local coordinate API for total-divergence lagrangians.

If `Bᵢ` is a jet-dependent current of order `k`, its total divergence

`∑ i, Dᵢ Bᵢ`

is naturally a lagrangian density of order `k + 1`. In the current Alpha stack, local lagrangians
carry their jet-coordinate derivatives as explicit data, so this module does not try to construct
that lagrangian automatically from the current. Instead, it packages the data needed by later
equivalence results:

- a local lagrangian of order `k + 1`,
- a current whose total divergence agrees with the lagrangian density along every field,
- and the Euler-Lagrange-triviality property of that lagrangian.

This keeps the API faithful to the standard total-divergence principle while avoiding premature
symbolic calculus for coordinate derivatives of total derivatives.

## ii. Key results

- `ClassicalFieldTheory.Local.HasTotalDivergenceDensity`
- `ClassicalFieldTheory.Local.IsEulerLagrangeTrivial`
- `ClassicalFieldTheory.Local.TotalDivergence`

## iii. Table of contents

- A. Total-divergence predicates
- B. Packaged total-divergence lagrangians

## iv. References

* J. Cortés and A. Haupt, Lecture Notes on Mathematical Methods of Classical Physics,
  arXiv:1612.03100v2, Chapter 5. [ref: cortes_haupt_2016]
-/

@[expose] public section

open Physlib
open scoped BigOperators

namespace ClassicalFieldTheory
namespace Local

/-!
## A. Total-divergence predicates

-/

/-- A lagrangian density has total-divergence form if, along every field, it is the sum of the
total derivatives of a jet-dependent current. A current of order `k` gives a density of order
`k + 1`. -/
def HasTotalDivergenceDensity (L : Lagrangian d m (k + 1))
    (current : Fin d → JetPoint d m k → ℝ) : Prop :=
  ∀ f : Space d → EuclideanSpace ℝ (Fin m),
    actionDensity L f = fun x => ∑ i : Fin d, totalDerivative k i (current i) f x

/-- A local lagrangian is Euler-Lagrange-trivial if its Euler-Lagrange operator vanishes along
every field. -/
def IsEulerLagrangeTrivial (L : Lagrangian d m k) : Prop :=
  ∀ f : Space d → EuclideanSpace ℝ (Fin m), eulerLagrangeOp L f = 0

/-!
## B. Packaged total-divergence lagrangians

-/

/-- A packaged local total divergence.

The current has order `k`, while the associated lagrangian has order `k + 1`, matching the
coordinate expression `L = ∑ i, Dᵢ Bᵢ`. The Euler-Lagrange-triviality field records the
variationally trivial direction needed by later equivalence results. -/
structure TotalDivergence (d m k : ℕ) where
  /-- The lagrangian represented by the total divergence of the current. -/
  lagrangian : Lagrangian d m (k + 1)
  /-- The current whose total divergence gives the lagrangian density. -/
  current : Fin d → JetPoint d m k → ℝ
  /-- The density agrees with the total divergence of the current along every field. -/
  hasTotalDivergenceDensity : HasTotalDivergenceDensity lagrangian current
  /-- The associated lagrangian is recorded as Euler-Lagrange-trivial. -/
  isEulerLagrangeTrivial : IsEulerLagrangeTrivial lagrangian

namespace TotalDivergence

variable {d m k : ℕ}

instance : CoeFun (TotalDivergence d m k) (fun _ => Lagrangian d m (k + 1)) where
  coe T := T.lagrangian

@[simp]
lemma actionDensity_eq (T : TotalDivergence d m k)
    (f : Space d → EuclideanSpace ℝ (Fin m)) :
    actionDensity T.lagrangian f =
      fun x => ∑ i : Fin d, totalDerivative k i (T.current i) f x :=
  T.hasTotalDivergenceDensity f

lemma eulerLagrangeOp_eq_zero (T : TotalDivergence d m k)
    (f : Space d → EuclideanSpace ℝ (Fin m)) :
    eulerLagrangeOp T.lagrangian f = 0 :=
  T.isEulerLagrangeTrivial f

lemma isCritical (T : TotalDivergence d m k)
    (f : Space d → EuclideanSpace ℝ (Fin m))
    (hTf : IsAdmissibleForAction T.lagrangian f)
    (hT : Lagrangian.SmoothInCoordinates T.lagrangian) :
    IsCritical T.lagrangian f := by
  exact
    (isCritical_iff_eulerLagrange_zero_of_admissibleForAction_and_smoothInCoordinates
      T.lagrangian f hTf hT).2 (T.eulerLagrangeOp_eq_zero f)

end TotalDivergence

end Local
end ClassicalFieldTheory
