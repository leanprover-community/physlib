/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.ProbabilisticTheory.OrderUnit.Archimedean
public import Physlib.ProbabilisticTheory.Channel.Reversible
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-!
# The observables of a C⋆-algebra

The self-adjoint part of a unital C⋆-algebra is an Archimedean order-unit space.

## i. Overview

The observables of a quantum system are the self-adjoint elements of its C⋆-algebra. One
observable lies below another if their difference has no negative measurement outcome. The
identity is the certain outcome.

Every observable lies below a multiple of the identity. So no outcome exceeds the norm.

An observable that lies below every positive multiple of the identity has no positive outcome.
This is the Archimedean property.

## ii. Key results

- `ProbabilisticTheory.selfAdjoint_le_nsmul_one_ceil_norm` : bound observables by natural
  multiples of the identity.
- `ProbabilisticTheory.selfAdjoint_le_zero_of_forall_pos_smul_one_le` : an observable below
  every positive multiple of the identity is nonpositive.
- `ProbabilisticTheory.ofCStarAlgebra` : the self-adjoint observables of a quantum system.
- `ProbabilisticTheory.realEquivComplex` : real outcomes are the self-adjoint complex scalars.

## iii. Table of contents

- A. The order-unit space of observables
- B. The Archimedean property
- C. Quantum observables and scalar outcomes

## iv. References

-/

@[expose] public section

open ComplexOrder

namespace ProbabilisticTheory

/-!

## A. The order-unit space of observables

-/

variable {𝒜 : Type*} [CStarAlgebra 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜]

/-- Nonnegative real scalars preserve the order on observables. -/
instance instPosSMulMonoSelfAdjoint : PosSMulMono ℝ (selfAdjoint 𝒜) where
  smul_le_smul_of_nonneg_left c hc a b hab := by
    rw [← Subtype.coe_le_coe] at hab ⊢
    exact smul_le_smul_of_nonneg_left hab hc

/-- Every observable lies below a natural multiple of the identity. -/
lemma selfAdjoint_le_nsmul_one_ceil_norm (x : selfAdjoint 𝒜) :
    x ≤ ⌈‖(x : 𝒜)‖⌉₊ • (1 : selfAdjoint 𝒜) := by
  have h0 : ((⌈‖(x : 𝒜)‖⌉₊ • (1 : selfAdjoint 𝒜) : selfAdjoint 𝒜) : 𝒜) =
      (⌈‖(x : 𝒜)‖⌉₊ : ℝ) • 1 := by
    rw [← Nat.cast_smul_eq_nsmul ℝ]
    rfl
  rw [← Subtype.coe_le_coe, h0]
  calc (x : 𝒜) ≤ algebraMap ℝ 𝒜 ‖(x : 𝒜)‖ := x.2.le_algebraMap_norm_self
    _ = ‖(x : 𝒜)‖ • (1 : 𝒜) := Algebra.algebraMap_eq_smul_one _
    _ ≤ (⌈‖(x : 𝒜)‖⌉₊ : ℝ) • (1 : 𝒜) := by gcongr; exact Nat.le_ceil _

/-!

## B. The Archimedean property

-/

/-- An observable below every positive multiple of the identity is below zero. -/
lemma selfAdjoint_le_zero_of_forall_pos_smul_one_le {x : selfAdjoint 𝒜}
    (h : ∀ ε : ℝ, 0 < ε → x ≤ ε • (1 : selfAdjoint 𝒜)) : x ≤ 0 := by
  have : Filter.Tendsto (fun ε : ℝ => ε • (1 : 𝒜)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds
      ((show Continuous fun ε : ℝ => ε • (1 : 𝒜) by fun_prop).tendsto' 0 0 (by simp))
  exact le_of_tendsto_of_tendsto (f := fun _ : ℝ => (x : 𝒜)) tendsto_const_nhds this
    (eventually_nhdsWithin_of_forall fun ε hε => h ε hε)

/-! ## C. Quantum observables and scalar outcomes -/

-- Keep the observable carrier transparent to subtype coercions.
/-- The self-adjoint elements of a C⋆-algebra, with their Archimedean order and unit. -/
noncomputable abbrev ofCStarAlgebra (𝒜 : Type*) [CStarAlgebra 𝒜] [PartialOrder 𝒜]
    [StarOrderedRing 𝒜] : ProbabilisticTheory where
  Observables := selfAdjoint 𝒜
  one_nonneg' := zero_le_one (α := 𝒜)
  exists_nsmul_one_le' x := ⟨_, selfAdjoint_le_nsmul_one_ceil_norm x⟩
  le_zero_of_forall_pos_smul_one_le' _ := selfAdjoint_le_zero_of_forall_pos_smul_one_le

/-- The real numbers are the observables of the quantum system with algebra `ℂ`. -/
noncomputable def realEquivComplex : Reversible real (ofCStarAlgebra ℂ) where
  toLinearEquiv := Complex.selfAdjointEquiv.symm
  map_le_map_iff' := by
    intro x y
    change (x : ℂ) ≤ (y : ℂ) ↔ x ≤ y
    simp
  map_one' := Subtype.ext rfl

end ProbabilisticTheory
