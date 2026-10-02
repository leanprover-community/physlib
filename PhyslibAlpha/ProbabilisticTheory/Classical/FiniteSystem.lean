/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.ProbabilisticTheory.Effect.Sharp
public import Physlib.ProbabilisticTheory.OrderUnit.Archimedean
public import PhyslibAlpha.ProbabilisticTheory.State.Convex
public import PhyslibAlpha.Mathematics.Geometry.Simplex
public import Mathlib.Topology.UnitInterval

/-!
# Finite classical systems

## i. Overview

A classical system with finitely many outcomes `ι` has as observables the real functions on `ι`,
ordered pointwise, with the constant function `1` as order unit. A state is then a probability
distribution on the outcomes: it gives outcome `i` the probability `ω (Pi.single i 1)`. So the
state space is the standard simplex, its pure states are the deterministic states reading off a
single outcome, and every state is a mixture of them in exactly one way. This is what makes the
system classical. The classical bit is `ι = Fin 2`.

## ii. Key results

- `FiniteClassicalSystem ι` : the classical system with outcomes `ι`.
- `FiniteClassicalSystem.stateEquiv` : the states are the probability vectors.
- `FiniteClassicalSystem.isPure_iff` : the pure states are the point evaluations.
- `FiniteClassicalSystem.isSimplex_algebraicStateSpace` : the state space is a simplex.

## iii. Table of contents

- A. The order-unit space
- B. States as probability vectors
- C. The simplex of states
- D. Effects of `ℝ`

-/

@[expose] public section

namespace ProbabilisticTheory

/-!

## A. The order-unit space

-/

/-- The classical system with outcomes `ι`: real functions on `ι`, ordered pointwise. -/
abbrev FiniteClassicalSystem (ι : Type*) : Type _ := ι → ℝ

namespace FiniteClassicalSystem

variable {ι : Type*} [Fintype ι]

instance : OrderUnitSpace (FiniteClassicalSystem ι) where
  one_nonneg _ := zero_le_one
  exists_nsmul_one_le A := ⟨∑ i, ⌈A i⌉₊, fun i => by
    simp only [Pi.smul_apply, Pi.one_apply, nsmul_eq_mul, mul_one, Nat.cast_sum]
    exact (Nat.le_ceil _).trans
      (Finset.single_le_sum (fun j _ => Nat.cast_nonneg ⌈A j⌉₊) (Finset.mem_univ i))⟩

instance : ArchimedeanOrderUnitSpace (FiniteClassicalSystem ι) where
  le_zero_of_forall_pos_smul_one_le A h i :=
    le_of_forall_pos_le_add fun ε hε => by simpa using h ε hε i

/-!

## B. States as probability vectors

-/

open UnitalPositiveLinearMap

/-- The deterministic state reading off the outcome `i`. -/
def eval (i : ι) : 𝓢[ℝ, FiniteClassicalSystem ι] :=
  ofLinearMap (LinearMap.proj i) (fun _ hA => hA i) rfl

@[simp] lemma eval_apply (i : ι) (A : FiniteClassicalSystem ι) : eval i A = A i := rfl

variable [DecidableEq ι]

/-- A linear functional is determined by its values on the outcomes. -/
lemma apply_eq_sum (f : FiniteClassicalSystem ι →ₗ[ℝ] ℝ) (A : FiniteClassicalSystem ι) :
    f A = ∑ i, A i * f (Pi.single i 1) := by
  have hA : A = ∑ i, A i • (Pi.single i 1 : ι → ℝ) := by
    ext j
    simp [Pi.single_apply]
  conv_lhs => rw [hA]
  simp [map_sum, map_smul]

/-- A linear functional on a classical system is its vector of values on the outcomes. -/
def dualEquiv : (FiniteClassicalSystem ι →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (ι → ℝ) where
  toFun f i := f (Pi.single i 1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun p := ∑ i, p i • LinearMap.proj i
  left_inv f := LinearMap.ext fun A => by simp [LinearMap.sum_apply, apply_eq_sum f A, mul_comm]
  right_inv p := funext fun i => by simp [LinearMap.sum_apply, Pi.single_apply]

@[simp]
lemma dualEquiv_apply (f : FiniteClassicalSystem ι →ₗ[ℝ] ℝ) (i : ι) :
    dualEquiv f i = f (Pi.single i 1) := rfl

@[simp]
lemma dualEquiv_symm_apply (p : ι → ℝ) (A : FiniteClassicalSystem ι) :
    dualEquiv.symm p A = ∑ i, p i * A i := by
  simp [dualEquiv, LinearMap.sum_apply]

/-- The state giving outcome `i` the probability `p i`. -/
def ofProbs (p : ι → ℝ) (hp : p ∈ stdSimplexSet ι) : 𝓢[ℝ, FiniteClassicalSystem ι] :=
  ofLinearMap (dualEquiv.symm p)
    (fun A hA => by simpa using Finset.sum_nonneg fun i _ => mul_nonneg (hp.1 i) (hA i))
    (by simpa using hp.2)

@[simp]
lemma ofProbs_apply (p : ι → ℝ) (hp : p ∈ stdSimplexSet ι) (A : FiniteClassicalSystem ι) :
    ofProbs p hp A = ∑ i, p i * A i :=
  dualEquiv_symm_apply p A

/-- The probability vectors are the images of the states. -/
lemma image_algebraicStateSpace :
    dualEquiv '' algebraicStateSpace (E := FiniteClassicalSystem ι) = stdSimplexSet ι := by
  ext p
  refine ⟨?_, fun hp => ⟨_, ⟨ofProbs p hp, rfl⟩, dualEquiv.apply_symm_apply p⟩⟩
  rintro ⟨_, ⟨ω, rfl⟩, rfl⟩
  refine ⟨fun i => map_nonneg ω (Pi.single_nonneg.2 zero_le_one), ?_⟩
  have h := apply_eq_sum ω.toLinearMap 1
  simp only [Pi.one_apply, one_mul] at h
  exact h.symm.trans (map_one ω)

/-- The states of a classical system are the probability vectors. -/
noncomputable def stateEquiv : 𝓢[ℝ, FiniteClassicalSystem ι] ≃ stdSimplexSet ι where
  toFun ω := ⟨dualEquiv ω.toLinearMap, by
    rw [← image_algebraicStateSpace]; exact ⟨_, ⟨ω, rfl⟩, rfl⟩⟩
  invFun p := ofProbs p p.2
  left_inv ω := toLinearMap_injective (dualEquiv.symm_apply_apply ω.toLinearMap)
  right_inv p := Subtype.ext (dualEquiv.apply_symm_apply (p : ι → ℝ))

@[simp]
lemma stateEquiv_apply (ω : 𝓢[ℝ, FiniteClassicalSystem ι]) (i : ι) :
    (stateEquiv ω : ι → ℝ) i = ω (Pi.single i 1) := rfl

/-!

## C. The simplex of states

-/

lemma dualEquiv_eval (i : ι) : dualEquiv (eval i).toLinearMap = Pi.single i 1 :=
  funext fun j => by
    change (Pi.single j (1 : ℝ) : ι → ℝ) i = (Pi.single i (1 : ℝ) : ι → ℝ) j
    simp [Pi.single_apply, eq_comm]

/-- The pure states are the deterministic states. -/
lemma isPure_iff {ω : 𝓢[ℝ, FiniteClassicalSystem ι]} : ω.IsPure ↔ ∃ i, ω = eval i := by
  rw [IsPure, ← dualEquiv.injective.mem_set_image, image_extremePoints, image_algebraicStateSpace,
    extremePoints_stdSimplexSet]
  simp only [Set.mem_range, ← dualEquiv_eval, dualEquiv.injective.eq_iff,
    toLinearMap_injective.eq_iff, eq_comm]

/-- **Classical systems are classical**: the state space is a simplex, so every state is a
mixture of the deterministic states in exactly one way. -/
lemma isSimplex_algebraicStateSpace :
    IsSimplex (algebraicStateSpace (E := FiniteClassicalSystem ι)) :=
  isSimplex_of_affineEquiv_stdSimplexSet dualEquiv.toAffineEquiv image_algebraicStateSpace

end FiniteClassicalSystem

/-!

## D. Effects of `ℝ`

-/

/-- The sharp effects of `ℝ` are `0` and `1`. -/
lemma Effect.isSharp_iff_eq_zero_or_eq_one {e : Effect ℝ} :
    Effect.IsSharp e ↔ (e : ℝ) = 0 ∨ (e : ℝ) = 1 := by
  simp [Effect.IsSharp, Set.extremePoints_Icc zero_le_one]

end ProbabilisticTheory
