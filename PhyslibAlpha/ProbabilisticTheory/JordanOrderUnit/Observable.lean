/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ProbabilisticTheory.JordanOrderUnit.Operator
public import PhyslibAlpha.ProbabilisticTheory.State.Basic
public import Physlib.ProbabilisticTheory.Effect.Sharp
public import PhyslibAlpha.ProbabilisticTheory.Effect.Basic
public import PhyslibAlpha.ProbabilisticTheory.Algebra.Statistics

/-!

# Moments, variance and Jordan projections

Moments and variance of observables, and Jordan projections as effects and compressions.

## i. Overview

The `n`-th moment of an observable `a` in a state `ω` is `ω(aⁿ)`, and the variance is `ω(a²) -
ω(a)²`. A Jordan projection is an observable `p` with `p ∘ p = p`, and two projections are
orthogonal when `p ∘ q = 0`. A Jordan projection is an effect, and its quadratic representation
`U_p` compresses onto it.

## ii. Key results

- `IsJordanOrderUnit.moment`, `IsJordanOrderUnit.variance` : moments and variance.
- `JordanAlgebra.IsJordanProjection`, `JordanAlgebra.JordanOrthogonal` : Jordan projections and
  orthogonality.
- `JordanAlgebra.IsJordanProjection.toEffect` : a projection as an effect.

## iii. Table of contents

- A. Moments and variance
- B. Jordan projections and orthogonality
- C. Projections as effects
- D. Compression: `U_p` for an idempotent `p`

## iv. References

* None.

-/

@[expose] public section

namespace ProbabilisticTheory

namespace IsJordanOrderUnit

open JordanAlgebra
open scoped JordanAlgebra

variable {E : Type*} [IsJordanOrderUnit E]

/-! ## A. Moments and variance -/

/-- The `n`-th moment of the observable `a` in the state `ω`: `moment_n(ω, a) = ω(a^n)`. -/
def moment (n : ℕ) (ω : 𝓢[ℝ, E]) (a : E) : ℝ := ω (a ^[n])

@[simp] lemma moment_zero (ω : 𝓢[ℝ, E]) (a : E) : moment 0 ω a = 1 := by
  change ω 1 = 1
  exact map_one ω

@[simp] lemma moment_one (ω : 𝓢[ℝ, E]) (a : E) : moment 1 ω a = ω a := by
  simp [moment]

/-- The variance of the observable `a` in the state `ω`, inherited from the generic covariance
form of its underlying linear functional. -/
def variance (ω : 𝓢[ℝ, E]) (a : E) : ℝ := LinearMap.variance ω.toLinearMap a

/-- The variance is expressed directly, unfolding `moment 2` to the Jordan square. -/
lemma variance_eq (ω : 𝓢[ℝ, E]) (a : E) : variance ω a = ω (a * a) - (ω a) ^ 2 := by
  simp [variance, LinearMap.variance, pow_two]
  rfl

/-- The second moment of any observable is nonnegative: it is the state's value on the
(possible-outcome) Jordan square. -/
lemma moment_two_nonneg (ω : 𝓢[ℝ, E]) (a : E) : 0 ≤ moment 2 ω a :=
  ω.map_nonneg (jpow_two a ▸ sq_nonneg a)

end IsJordanOrderUnit

namespace JordanAlgebra

variable {E : Type*}

open scoped JordanAlgebra

/-! ## B. Jordan projections and orthogonality -/

section Algebraic

variable [NonAssocCommRing E]

/-- A Jordan projection: an element idempotent for the Jordan product, `p ∘ p = p`. The
Jordan-algebraic analogue of a self-adjoint projection, and (in the canonical C⋆-algebra
realization) exactly an ordinary projection `p² = p = p⋆`. -/
def IsJordanProjection (p : E) : Prop := p * p = p

/-- Two elements are Jordan-orthogonal when their Jordan product vanishes, `p ∘ q = 0`: the
Jordan-algebraic analogue of `Effect.Orthogonal`. -/
def JordanOrthogonal (p q : E) : Prop := p * q = 0

lemma isJordanProjection_zero : IsJordanProjection (0 : E) := by
  simp [IsJordanProjection]

lemma isJordanProjection_one : IsJordanProjection (1 : E) := _root_.mul_one 1

lemma jordanOrthogonal_comm {p q : E} (h : JordanOrthogonal p q) : JordanOrthogonal q p := by
  unfold JordanOrthogonal at *
  rwa [mul_comm]

lemma jordanOrthogonal_zero_left (p : E) : JordanOrthogonal 0 p := by
  simp [JordanOrthogonal]

lemma jordanOrthogonal_zero_right (p : E) : JordanOrthogonal p 0 :=
  jordanOrthogonal_comm (jordanOrthogonal_zero_left p)

end Algebraic

section Ordered

variable [IsJordanOrderUnit E]

/-- A Jordan projection is automatically a possible outcome (`0 ≤ p`), since it equals its own
Jordan square. -/
lemma IsJordanProjection.nonneg {p : E} (hp : IsJordanProjection p) : 0 ≤ p :=
  hp ▸ IsJordanOrderUnit.sq_nonneg p

/-- The sum of two orthogonal Jordan projections is again a Jordan projection: the abstract,
operator-free analogue of "two orthogonal projections add to a projection", the algebraic content
behind an event-logic (sharp-effect) sum. -/
lemma IsJordanProjection.add_of_jordanOrthogonal {p q : E} (hp : IsJordanProjection p)
    (hq : IsJordanProjection q) (horth : JordanOrthogonal p q) :
    IsJordanProjection (p + q) := by
  unfold IsJordanProjection at *
  unfold JordanOrthogonal at horth
  rw [add_mul, mul_add, mul_add, hp, hq, horth, mul_comm q p, horth]
  abel

/-- The complement `1 - p` of a Jordan projection is again a Jordan projection: the Jordan-algebra
analogue of `Effect.complement`. -/
lemma IsJordanProjection.complement {p : E} (hp : IsJordanProjection p) :
    IsJordanProjection (1 - p) := by
  unfold IsJordanProjection at *
  rw [IsJordanOrderUnit.one_sub_mul_one_sub, hp]
  abel

/-- A Jordan projection is orthogonal to its own complement: `p ∘ (1 - p) = 0`. -/
lemma IsJordanProjection.jordanOrthogonal_complement {p : E} (hp : IsJordanProjection p) :
    JordanOrthogonal p (1 - p) := by
  unfold IsJordanProjection at hp
  unfold JordanOrthogonal
  rw [IsJordanOrderUnit.mul_one_sub, hp]
  abel

/-! ## C. Projections as effects -/

/-- A Jordan projection is bounded above by the order unit. Its complement is another projection,
hence a nonnegative square, and `0 ≤ 1 - p` is exactly `p ≤ 1`. -/
lemma IsJordanProjection.le_one {p : E} (hp : IsJordanProjection p) : p ≤ 1 :=
  sub_nonneg.mp hp.complement.nonneg

/-- A Jordan projection, bundled as an effect. -/
def IsJordanProjection.toEffect {p : E} (hp : IsJordanProjection p) : Effect E :=
  ⟨p, hp.nonneg, hp.le_one⟩

@[simp]
lemma IsJordanProjection.coe_toEffect {p : E} (hp : IsJordanProjection p) :
    (hp.toEffect : E) = p := rfl

/-- Bundling a projection's algebraic complement agrees with taking its effect complement. -/
lemma IsJordanProjection.toEffect_complement {p : E} (hp : IsJordanProjection p) :
    hp.complement.toEffect = Effect.complement hp.toEffect := rfl

/-- Jordan-orthogonal projections have a defined partial sum in the effect algebra. This is the
forward direction that follows from square positivity alone; the converse needs the stronger JB
order theory. -/
lemma IsJordanProjection.effectOrthogonal_of_jordanOrthogonal {p q : E}
    (hp : IsJordanProjection p) (hq : IsJordanProjection q) (hpq : JordanOrthogonal p q) :
    Effect.Orthogonal hp.toEffect hq.toEffect :=
  (hp.add_of_jordanOrthogonal hq hpq).le_one

/-- The effect-algebra partial sum of Jordan-orthogonal projections is their algebraic projection
sum. -/
lemma IsJordanProjection.addOfOrthogonal_toEffect {p q : E}
    (hp : IsJordanProjection p) (hq : IsJordanProjection q) (hpq : JordanOrthogonal p q) :
    Effect.addOfOrthogonal hp.toEffect hq.toEffect
      (hp.effectOrthogonal_of_jordanOrthogonal hq hpq) =
        (hp.add_of_jordanOrthogonal hq hpq).toEffect := by
  rfl

end Ordered

/-! ## D. Compression: `U_p` for an idempotent `p` -/

section Compression

variable [NonAssocCommRing E] [Module ℝ E] [SMulCommClass ℝ E E]

/-- **Compression onto an event.** For a Jordan projection `p`, `U_p(p) = p`: compressing `p`
itself onto the event `p` changes nothing. The Jordan-algebraic seed of "the outcome that already
happened is unaffected by conditioning on it having happened". -/
lemma IsJordanProjection.quadRep_self {p : E} (hp : IsJordanProjection p) : U p p = p := by
  have h1 : p * (p * p) = p := by rw [hp, hp]
  have h2 : p ^[2] * p = p := by rw [jpow_two, hp, hp]
  rw [quadRep_apply, h1, h2]
  module

/-- `U_p q = 0` for projections `q` orthogonal to `p`. -/
lemma IsJordanProjection.quadRep_jordanOrthogonal {p q : E} (hp : IsJordanProjection p)
    (horth : JordanOrthogonal p q) : U p q = 0 := by
  unfold JordanOrthogonal at horth
  have h1 : p * (p * q) = 0 := by rw [horth, mul_zero]
  have h2 : p ^[2] * q = 0 := by rw [jpow_two, hp, horth]
  rw [quadRep_apply, h1, h2]
  module

/-- **Compression of the unit recovers the event itself.** For a Jordan projection `p`,
`U_p(1) = p`: this is `quadRep_apply_one` specialized using `p² = p`. -/
lemma IsJordanProjection.quadRep_one {p : E} (hp : IsJordanProjection p) : U p (1 : E) = p := by
  rw [quadRep_apply_one, jpow_two, hp]

end Compression

end JordanAlgebra

end ProbabilisticTheory
