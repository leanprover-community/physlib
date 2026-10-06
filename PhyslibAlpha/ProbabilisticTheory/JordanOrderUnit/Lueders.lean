/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ProbabilisticTheory.JordanOrderUnit.Quadratic.Order
public import PhyslibAlpha.ProbabilisticTheory.JordanOrderUnit.Conditioning
public import PhyslibAlpha.ProbabilisticTheory.JordanOrderUnit.JB.GeneratedByOne.SqrtUniqueness
public import PhyslibAlpha.ProbabilisticTheory.Channel.Operation

/-!

# Lüders operations

Lüders operations `x ↦ U_{√e} x` of effects and the states conditioned on effects.

## i. Overview

An effect `e` of an ordered JB-algebra has a positive square root. The Lüders operation of `e` is
the quadratic representation `x ↦ U_{√e} x`, and conditioning a state on `e` is `x ↦ ω(U_{√e} x) /
ω(e)`. For a projection this is conditioning on the projection.

## ii. Key results

- `NormedJordanAlgebra.luedersMap` : the Lüders map of an effect.
- `NormedJordanAlgebra.luedersOperation` : the Lüders operation.
- `NormedJordanAlgebra.luedersCondition` : the state conditioned on an effect.
- `NormedJordanAlgebra.luedersCondition_isNormal` : conditioning preserves normality.

## iii. Table of contents

- A. The Lüders operation
- B. Lüders operations of projections
- C. Lüders conditioning

## iv. References

* None.

-/

@[expose] public section

namespace ProbabilisticTheory

namespace NormedJordanAlgebra

open JordanAlgebra
open scoped JordanAlgebra

variable {E : Type*} [IsJBOrderUnit E] [Nontrivial E]
  [IsQuadraticallyPositive E]

/-! ## A. The Lüders operation -/

/-- The intrinsic positive square root selected by the JB continuous functional calculus for an
effect. -/
noncomputable def effectSqrt (e : Effect E) : E :=
  jordanSqrt (e : E) e.2.1

/-- The Lüders operation of an effect: the positive quadratic operation induced by its square
root.  In a special Jordan algebra it is precisely `x ↦ sqrt(e) x sqrt(e)`. -/
noncomputable def luedersMap (e : Effect E) : E →ₚ[ℝ] E :=
  quadRepPositiveLinearMap (effectSqrt e)

@[simp]
lemma luedersMap_apply (e : Effect E) (x : E) : luedersMap e x = U (effectSqrt e) x :=
  rfl

/-- A Lüders operation sends the order unit to its effect.  Thus its probability in a state is
exactly the probability assigned to that effect. -/
lemma luedersMap_one (e : Effect E) : luedersMap e (1 : E) = e := by
  rw [luedersMap_apply, quadRep_apply_one, jpow_two]
  exact jordanSqrt_mul_self (e : E) e.2.1

/-- The Lüders map is an operation: it is positive and its outcome probability never exceeds
certainty.  Its outcome effect is the original effect, so this is the intrinsic Jordan analogue
of a single-Kraus measurement operation. -/
noncomputable def luedersOperation (e : Effect E) : Operation E :=
  ⟨luedersMap e, by simpa only [luedersMap_one] using e.2.2⟩

@[simp]
lemma luedersOperation_apply (e : Effect E) (x : E) : luedersOperation e x = luedersMap e x :=
  rfl

/-- The effect recorded by the Lüders operation is exactly the effect it implements. -/
lemma luedersOperation_outcomeEffect (e : Effect E) :
    (Operation.outcomeEffect (luedersOperation e) : E) = e := by
  rw [Operation.coe_outcomeEffect, luedersOperation_apply, luedersMap_one]

/-! ## B. Lüders operations of projections -/

omit [IsQuadraticallyPositive E] in
/-- The CFC square root of a sharp Jordan event is the event itself.  This is the point where
the general effect operation recovers projection compression. -/
lemma effectSqrt_toEffect_of_projection {p : E} (hp : IsJordanProjection p) :
    effectSqrt hp.toEffect = p := by
  change jordanSqrt p hp.nonneg = p
  exact (jordanSqrt_eq_of_nonneg_of_mul_self p hp.nonneg p hp.nonneg hp).symm

/-- Lüders filtering by a sharp event is exactly quadratic compression by that projection. -/
lemma luedersMap_toEffect_of_projection {p : E} (hp : IsJordanProjection p) :
    luedersMap hp.toEffect = quadRepPositiveLinearMap p := by
  rw [luedersMap, effectSqrt_toEffect_of_projection hp]

/-! ## C. Lüders conditioning -/

/-- The normalized post-measurement state associated with an effect of nonzero probability. -/
noncomputable def luedersCondition (ω : 𝓢[ℝ, E]) (e : Effect E) (hmass : 0 < ω e) :
    𝓢[ℝ, E] :=
  (luedersOperation e).condition ω (by
    simpa only [luedersOperation_apply, luedersMap_one] using hmass)

/-- Formula for the normalized state after the Lüders operation. -/
@[simp]
lemma luedersCondition_apply (ω : 𝓢[ℝ, E]) (e : Effect E) (hmass : 0 < ω e) (x : E) :
    luedersCondition ω e hmass x = (ω e)⁻¹ * ω (U (effectSqrt e) x) := by
    rw [luedersCondition, Operation.condition_apply]
    change (ω (luedersOperation e 1))⁻¹ * ω (luedersOperation e x) =
      (ω e)⁻¹ * ω (U (effectSqrt e) x)
    rw [luedersOperation_apply, luedersMap_one, luedersOperation_apply, luedersMap_apply]

/-- The normalized Lüders state evaluates the unit to one. -/
lemma luedersCondition_one (ω : 𝓢[ℝ, E]) (e : Effect E) (hmass : 0 < ω e) :
    luedersCondition ω e hmass 1 = 1 :=
  map_one (luedersCondition ω e hmass)

/-- In a JBW application, once the Lüders operation is known to preserve directed suprema,
conditioning a normal state by a nonzero-probability effect remains normal.  Normality of the
quadratic operation itself is the remaining intrinsic JBW quadratic-order theorem. -/
lemma luedersCondition_isNormal (ω : 𝓢[ℝ, E]) (e : Effect E) (hmass : 0 < ω e)
    (hOp : (luedersOperation e).IsNormal) (hω : ω.IsNormal) :
    (luedersCondition ω e hmass).IsNormal :=
  Operation.condition_isNormal (luedersOperation e) ω (by
    simpa only [luedersOperation_apply, luedersMap_one] using hmass) hOp hω

/-- For a projection, conditioning on the effect is conditioning on the projection. -/
lemma luedersCondition_toEffect_of_projection {p : E} (hp : IsJordanProjection p)
    (ω : 𝓢[ℝ, E]) (hmass : 0 < ω p) :
    luedersCondition ω hp.toEffect hmass = hp.conditionOfQuadraticPositive ω hmass := by
  apply UnitalPositiveLinearMap.ext
  intro x
  have hmass' : 0 < ω (hp.toEffect : E) := by simpa using hmass
  change luedersCondition ω hp.toEffect hmass' x =
    hp.conditionOfQuadraticPositive ω hmass x
  rw [luedersCondition_apply, IsJordanProjection.conditionOfQuadraticPositive_apply,
    effectSqrt_toEffect_of_projection hp]
  simp only [hp.coe_toEffect]

end NormedJordanAlgebra

end ProbabilisticTheory
