/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.ProbabilisticTheory.State.Basic
public import Physlib.ProbabilisticTheory.CStarAlgebra.Channel
public import Physlib.ProbabilisticTheory.CStarAlgebra.Traciality

/-!
# States of a C⋆-algebra

States inherit complex extension from channels and can be characterized by traciality.

## i. Overview

A state assigns real expectation values to self-adjoint operators, the observables.
Every operator has a decomposition into self-adjoint parts, its real and imaginary part.
Applying states onto these two parts is a unique extension to a complex-linear map and vice versa.
Therefore complex-linear maps are in bijection with their restriction to self-adjoint operators.

A state is a channel into ℝ. The scalar identification
`realEquivComplex` lets it inherit complex extension from the channel construction.
A tracial state assigns the same expectation to the positive observables `a⋆a` and `aa⋆`.
Equivalently its complex extension is cyclic on products.

## ii. Key results

- `ProbabilisticTheory.State.extend` : complex expectation values on all operators.
- `ProbabilisticTheory.State.complexEquiv` : states correspond to normalized positive
  complex-linear functionals.
- `ProbabilisticTheory.State.extend_comap` : extension respects state pullback.
- `ProbabilisticTheory.State.IsTracial` : equality of expectations on `a⋆a` and `aa⋆`.
- `ProbabilisticTheory.State.isTracial_iff_extend_map_mul_comm` : traciality is equivalent to
  cyclicity of the complex extension.

## iii. Table of contents

- A. States on all operators
- B. Tracial states

## iv. References

-/

@[expose] public section

open ProbabilisticTheory ComplexOrder

namespace ProbabilisticTheory.State

variable {𝒜 ℬ : Type*} [CStarAlgebra 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  [CStarAlgebra ℬ] [PartialOrder ℬ] [StarOrderedRing ℬ]

/-! ## A. States on all operators -/

/-- Extend the expectation values of observables to all operators. -/
noncomputable def extend (ω : (ofCStarAlgebra 𝒜).State) : 𝒜 →ₚ[ℂ] ℂ :=
  (realEquivComplex.toChannel.comp ω).extend

/-- Extension preserves the expectation value of every observable. -/
@[simp]
lemma extend_apply (ω : (ofCStarAlgebra 𝒜).State) (A : selfAdjoint 𝒜) :
    ω.extend (A : 𝒜) = (ω A : ℂ) :=
  (realEquivComplex.toChannel.comp ω).extend_apply A

/-- The extended state is normalized. -/
@[simp]
lemma extend_one (ω : (ofCStarAlgebra 𝒜).State) : ω.extend 1 = 1 :=
  (realEquivComplex.toChannel.comp ω).extend_one

/-- Extending a pulled-back state agrees with composing the extensions. -/
lemma extend_comap (Φ : Channel (ofCStarAlgebra 𝒜) (ofCStarAlgebra ℬ))
    (ω : (ofCStarAlgebra ℬ).State) : (ω.comap Φ).extend = ω.extend.comp Φ.extend :=
  Channel.extend_comp (realEquivComplex.toChannel.comp ω) Φ

/-- States of a quantum system are the same as normalized positive functionals on all its
operators. -/
noncomputable def complexEquiv (𝒜 : Type*) [CStarAlgebra 𝒜] [PartialOrder 𝒜]
    [StarOrderedRing 𝒜] : (ofCStarAlgebra 𝒜).State ≃ {f : 𝒜 →ₚ[ℂ] ℂ // f 1 = 1} :=
  Equiv.trans
    { toFun := realEquivComplex.toChannel.comp
      invFun := realEquivComplex.symm.toChannel.comp
      left_inv ω := Channel.ext fun A => realEquivComplex.symm_apply_apply (ω A)
      right_inv Φ := Channel.ext fun A => realEquivComplex.apply_symm_apply (Φ A) }
    (Channel.complexEquiv (𝒜 := 𝒜) (ℬ := ℂ))

/-! ## B. Tracial states -/

/-- A state is tracial when `a⋆a` and `aa⋆` have the same expectation for every operator `a`. -/
def IsTracial (ω : (ofCStarAlgebra 𝒜).State) : Prop :=
  ∀ a : 𝒜, ω ⟨star a * a, .star_mul_self a⟩ = ω ⟨a * star a, .mul_star_self a⟩

/-- A state is tracial exactly when its complex extension is cyclic on products. -/
lemma isTracial_iff_extend_map_mul_comm (ω : (ofCStarAlgebra 𝒜).State) :
    ω.IsTracial ↔ ∀ a b : 𝒜, ω.extend (a * b) = ω.extend (b * a) := by
  refine Iff.trans ?_
    (LinearMap.map_mul_comm_iff_star_mul_self_eq_mul_star_self ω.extend.toLinearMap).symm
  constructor
  · intro h a
    exact (extend_apply ω ⟨_, .star_mul_self a⟩).trans
      ((congrArg Complex.ofReal (h a)).trans (extend_apply ω ⟨_, .mul_star_self a⟩).symm)
  · intro h a
    apply Complex.ofReal_injective
    exact (extend_apply ω ⟨_, .star_mul_self a⟩).symm.trans
      ((h a).trans (extend_apply ω ⟨_, .mul_star_self a⟩))

/-- A tracial state does not see the order of a product. -/
lemma IsTracial.map_mul_comm {ω : (ofCStarAlgebra 𝒜).State} (h : ω.IsTracial) (a b : 𝒜) :
    ω.extend (a * b) = ω.extend (b * a) :=
  (isTracial_iff_extend_map_mul_comm ω).mp h a b

/-- A tracial state vanishes on commutators. -/
lemma IsTracial.map_commutator {ω : (ofCStarAlgebra 𝒜).State} (h : ω.IsTracial) (a b : 𝒜) :
    ω.extend (a * b - b * a) = 0 := by
  rw [map_sub, h.map_mul_comm a b, sub_self]

/-- A tracial state is invariant under the change of frame `x ↦ u * x * u⋆` by a unitary. -/
lemma IsTracial.map_conj {ω : (ofCStarAlgebra 𝒜).State} (h : ω.IsTracial) (u : unitary 𝒜)
    (x : 𝒜) : ω.extend (u * x * star (u : 𝒜)) = ω.extend x := by
  simpa [← mul_assoc] using h.map_mul_comm (u * x) (star (u : 𝒜))

/-- A state is tracial if and only if `ω (a⋆ * a) = ω (a * a⋆)` for all `a`. -/
lemma isTracial_iff_star_mul_self_eq_mul_star_self (ω : (ofCStarAlgebra 𝒜).State) :
    ω.IsTracial ↔ ∀ a : 𝒜, ω.extend (star a * a) = ω.extend (a * star a) :=
  (isTracial_iff_extend_map_mul_comm ω).trans
    (LinearMap.map_mul_comm_iff_star_mul_self_eq_mul_star_self ω.extend.toLinearMap)

end ProbabilisticTheory.State
