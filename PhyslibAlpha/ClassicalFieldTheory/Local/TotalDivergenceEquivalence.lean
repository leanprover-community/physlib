/-
Copyright (c) 2026 Juan Jose Fernandez Morales. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Jose Fernandez Morales
-/
module

public import PhyslibAlpha.ClassicalFieldTheory.Local.TotalDivergence
/-!
# Lagrangian equivalence up to total divergences

Lagrangians differing by a total divergence have the same Euler-Lagrange equations.

## i. Overview

This module adds the local coordinate API for lagrangians that differ by a total divergence.

In the current Alpha stack, local lagrangians carry their jet-coordinate derivatives explicitly.
Consequently, this module does not construct the modified lagrangian by adding a current
divergence syntactically. Instead, it packages the data needed by later equivalence results:

- two local lagrangians of the same order,
- a total-divergence lagrangian witnessing the density difference,
- and equality of the corresponding Euler-Lagrange operators.

This is the field-theory analogue of the classical fact that adding a total derivative or total
divergence does not change the variational equations, while keeping the current API honest about
which facts are data and which facts are proved.

## ii. Key results

- `ClassicalFieldTheory.Local.HasTotalDivergenceDifference`
- `ClassicalFieldTheory.Local.IsEulerLagrangeEquivalent`
- `ClassicalFieldTheory.Local.IsEulerLagrangeEquivalent.eulerLagrangeOp_eq_zero_iff`
- `ClassicalFieldTheory.Local.IsEulerLagrangeEquivalent.isCritical_iff`
- `ClassicalFieldTheory.Local.TotalDivergenceEquivalence`
- `ClassicalFieldTheory.Local.TotalDivergenceEquivalence.isCritical_iff`

## iii. Table of contents

- A. Equivalence predicates
- B. Euler-Lagrange equivalence API
- C. Packaged total-divergence equivalences

## iv. References

* J. Cortés and A. Haupt, Lecture Notes on Mathematical Methods of Classical Physics,
  arXiv:1612.03100v2, Chapter 5. [ref: cortes_haupt_2016]
-/

@[expose] public section

namespace ClassicalFieldTheory
namespace Local

/-!
## A. Equivalence predicates

-/

/-- A lagrangian `target` differs from `source` by the density of a packaged total divergence.

The total divergence has current order `k`, hence its associated lagrangian and both compared
lagrangians have order `k + 1`. -/
def HasTotalDivergenceDifference (source target : Lagrangian d m (k + 1))
    (T : TotalDivergence d m k) : Prop :=
  ∀ f : Space d → EuclideanSpace ℝ (Fin m),
    actionDensity target f =
      fun x => actionDensity source f x + actionDensity T.lagrangian f x

/-- Two local lagrangians are Euler-Lagrange equivalent when they determine the same local
Euler-Lagrange operator along every field. -/
def IsEulerLagrangeEquivalent (source target : Lagrangian d m k) : Prop :=
  ∀ f : Space d → EuclideanSpace ℝ (Fin m),
    eulerLagrangeOp target f = eulerLagrangeOp source f

/-!
## B. Euler-Lagrange equivalence API

-/

namespace IsEulerLagrangeEquivalent

variable {d m k : ℕ}

lemma refl (L : Lagrangian d m k) : IsEulerLagrangeEquivalent L L := by
  intro f
  rfl

lemma symm {L1 L2 : Lagrangian d m k} (h : IsEulerLagrangeEquivalent L1 L2) :
    IsEulerLagrangeEquivalent L2 L1 := by
  intro f
  exact (h f).symm

lemma trans {L1 L2 L3 : Lagrangian d m k}
    (h12 : IsEulerLagrangeEquivalent L1 L2) (h23 : IsEulerLagrangeEquivalent L2 L3) :
    IsEulerLagrangeEquivalent L1 L3 := by
  intro f
  exact (h23 f).trans (h12 f)

lemma eulerLagrangeOp_eq {source target : Lagrangian d m k}
    (h : IsEulerLagrangeEquivalent source target)
    (f : Space d → EuclideanSpace ℝ (Fin m)) :
    eulerLagrangeOp target f = eulerLagrangeOp source f :=
  h f

lemma eulerLagrangeOp_eq_zero_iff {source target : Lagrangian d m k}
    (h : IsEulerLagrangeEquivalent source target)
    (f : Space d → EuclideanSpace ℝ (Fin m)) :
    eulerLagrangeOp target f = 0 ↔ eulerLagrangeOp source f = 0 := by
  rw [h.eulerLagrangeOp_eq f]

lemma isCritical_iff {source target : Lagrangian d m k}
    (h : IsEulerLagrangeEquivalent source target)
    (f : Space d → EuclideanSpace ℝ (Fin m))
    (hsourcef : IsAdmissibleForAction source f)
    (htargetf : IsAdmissibleForAction target f)
    (hsource : Lagrangian.SmoothInCoordinates source)
    (htarget : Lagrangian.SmoothInCoordinates target) :
    IsCritical target f ↔ IsCritical source f := by
  rw [isCritical_iff_eulerLagrange_zero_of_admissibleForAction_and_smoothInCoordinates
      target f htargetf htarget,
    isCritical_iff_eulerLagrange_zero_of_admissibleForAction_and_smoothInCoordinates
      source f hsourcef hsource,
    h f]

lemma isCritical_target_of_source {source target : Lagrangian d m k}
    (h : IsEulerLagrangeEquivalent source target)
    (f : Space d → EuclideanSpace ℝ (Fin m))
    (hsourcef : IsAdmissibleForAction source f)
    (htargetf : IsAdmissibleForAction target f)
    (hsource : Lagrangian.SmoothInCoordinates source)
    (htarget : Lagrangian.SmoothInCoordinates target)
    (hcrit : IsCritical source f) :
    IsCritical target f :=
  (h.isCritical_iff f hsourcef htargetf hsource htarget).2 hcrit

lemma isCritical_source_of_target {source target : Lagrangian d m k}
    (h : IsEulerLagrangeEquivalent source target)
    (f : Space d → EuclideanSpace ℝ (Fin m))
    (hsourcef : IsAdmissibleForAction source f)
    (htargetf : IsAdmissibleForAction target f)
    (hsource : Lagrangian.SmoothInCoordinates source)
    (htarget : Lagrangian.SmoothInCoordinates target)
    (hcrit : IsCritical target f) :
    IsCritical source f :=
  (h.isCritical_iff f hsourcef htargetf hsource htarget).1 hcrit

end IsEulerLagrangeEquivalent

/-!
## C. Packaged total-divergence equivalences

-/

/-- A packaged equivalence between two local lagrangians whose densities differ by a total
divergence.

The field `sameEulerLagrangeOp` records the variational consequence in the current Alpha API. It
will become a theorem once the stack has enough symbolic calculus for coordinate derivatives of
total divergences. -/
structure TotalDivergenceEquivalence (d m k : ℕ) where
  /-- The original local lagrangian. -/
  source : Lagrangian d m (k + 1)
  /-- The modified local lagrangian. -/
  target : Lagrangian d m (k + 1)
  /-- The total divergence giving the density difference. -/
  divergence : TotalDivergence d m k
  /-- The target density is the source density plus the total-divergence density. -/
  hasTotalDivergenceDifference :
    HasTotalDivergenceDifference source target divergence
  /-- The two lagrangians have the same Euler-Lagrange operator. -/
  sameEulerLagrangeOp : IsEulerLagrangeEquivalent source target

namespace TotalDivergenceEquivalence

variable {d m k : ℕ}

@[simp]
lemma actionDensity_eq (E : TotalDivergenceEquivalence d m k)
    (f : Space d → EuclideanSpace ℝ (Fin m)) :
    actionDensity E.target f =
      fun x => actionDensity E.source f x + actionDensity E.divergence.lagrangian f x :=
  E.hasTotalDivergenceDifference f

lemma eulerLagrangeOp_eq (E : TotalDivergenceEquivalence d m k)
    (f : Space d → EuclideanSpace ℝ (Fin m)) :
    eulerLagrangeOp E.target f = eulerLagrangeOp E.source f :=
  E.sameEulerLagrangeOp f

lemma eulerLagrangeOp_eq_zero_iff (E : TotalDivergenceEquivalence d m k)
    (f : Space d → EuclideanSpace ℝ (Fin m)) :
    eulerLagrangeOp E.target f = 0 ↔ eulerLagrangeOp E.source f = 0 :=
  E.sameEulerLagrangeOp.eulerLagrangeOp_eq_zero_iff f

lemma isCritical_iff (E : TotalDivergenceEquivalence d m k)
    (f : Space d → EuclideanSpace ℝ (Fin m))
    (hsourcef : IsAdmissibleForAction E.source f)
    (htargetf : IsAdmissibleForAction E.target f)
    (hsource : Lagrangian.SmoothInCoordinates E.source)
    (htarget : Lagrangian.SmoothInCoordinates E.target) :
    IsCritical E.target f ↔ IsCritical E.source f := by
  exact E.sameEulerLagrangeOp.isCritical_iff f hsourcef htargetf hsource htarget

lemma isCritical_target_of_source (E : TotalDivergenceEquivalence d m k)
    (f : Space d → EuclideanSpace ℝ (Fin m))
    (hsourcef : IsAdmissibleForAction E.source f)
    (htargetf : IsAdmissibleForAction E.target f)
    (hsource : Lagrangian.SmoothInCoordinates E.source)
    (htarget : Lagrangian.SmoothInCoordinates E.target)
    (hcrit : IsCritical E.source f) :
    IsCritical E.target f :=
  E.sameEulerLagrangeOp.isCritical_target_of_source f hsourcef htargetf hsource htarget hcrit

lemma isCritical_source_of_target (E : TotalDivergenceEquivalence d m k)
    (f : Space d → EuclideanSpace ℝ (Fin m))
    (hsourcef : IsAdmissibleForAction E.source f)
    (htargetf : IsAdmissibleForAction E.target f)
    (hsource : Lagrangian.SmoothInCoordinates E.source)
    (htarget : Lagrangian.SmoothInCoordinates E.target)
    (hcrit : IsCritical E.target f) :
    IsCritical E.source f :=
  E.sameEulerLagrangeOp.isCritical_source_of_target f hsourcef htargetf hsource htarget hcrit

end TotalDivergenceEquivalence

end Local
end ClassicalFieldTheory
