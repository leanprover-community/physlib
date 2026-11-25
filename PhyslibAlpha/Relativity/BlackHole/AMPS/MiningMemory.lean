/-
Copyright (c) 2026 AMPS formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AMPS formalization contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Tactic.NormNum

/-!
# Mining memory and a common thermalization map

The common thermalization map.

## i. Overview

AMPS, arXiv:1207.3123v4, §3.2, first allows an N-bit black-hole state to emit
a Bell pair. One member is inside and the other is stored in the mining
equipment. The equipment can apply an arbitrary local qubit unitary before
thermalization. We retain the paper's unnormalized Bell vector, whose squared
norm is two; multiplying every preparation by the same normalization leaves
its span unchanged.

With no additional system recording the operation, a single closed-system
evolution must preserve inner products on the span of the allowed inputs,
including superpositions. For each fixed storage unitary on its own, the
original black-hole label still ranges over just D states. Allowing the
operation to vary expands the common input span to dimension 4D. The proposed
endpoint has N−1 black-hole bits and one storage bit, hence dimension D.

## ii. Key results

* `pauli_unitary`
* `fixed_unitary_dimension`

## iii. Table of contents

- A. The common thermalization map

## iv. References

* [ref: Almheiri2013]

## A. The common thermalization map
-/

@[expose] public section

noncomputable section

namespace AMPS.MiningMemory

open scoped InnerProductSpace

/-- Complex amplitudes of the interior and storage qubits. -/
abbrev Pair := EuclideanSpace ℂ (Bool × Bool)

/-- The four local Pauli choices I, X, Z and XZ (the last differs from Y by a phase).
The first bit selects a basis flip, and the second selects the input-dependent sign. -/
def pauli (a : Bool × Bool) : Matrix Bool Bool ℂ := fun out inp =>
  if out = (if a.1 then !inp else inp) then (if a.2 && inp then -1 else 1) else 0

lemma pauli_unitary (a : Bool × Bool) : pauli a ∈ Matrix.unitaryGroup Bool ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  ext i j
  obtain ⟨f, s⟩ := a
  cases f <;> cases s <;> cases i <;> cases j <;>
    norm_num [pauli, Matrix.mul_apply, Matrix.star_apply, Fintype.sum_bool, Matrix.one_apply]

/-- Acting on the storage qubit of ∑ₖ |k;k⟩ gives coefficients U(out,k).
The interior basis coordinate k is untouched. -/
def transformedBell (U : Matrix Bool Bool ℂ) : Pair :=
  WithLp.toLp 2 (fun p => ∑ k : Bool, (if p.1 = k then 1 else 0) * U p.2 k)

private lemma bell_gram (a b : Bool × Bool) :
    inner ℂ (transformedBell (pauli a)) (transformedBell (pauli b)) = if a = b then 2 else 0 := by
  rw [PiLp.inner_apply, Fintype.sum_prod_type]
  obtain ⟨f, s⟩ := a
  obtain ⟨g, t⟩ := b
  cases f <;> cases s <;> cases g <;> cases t <;>
    norm_num [transformedBell, pauli, Fintype.sum_bool, RCLike.inner_apply]

variable {J : Type*} [Fintype J] [DecidableEq J]

/-- Preparation from the original memory basis state j after an operation on
the external storage bit. Coordinates retain the memory, interior and storage labels. -/
def prepare (j : J) (U : Matrix Bool Bool ℂ) : EuclideanSpace ℂ (J × (Bool × Bool)) :=
  WithLp.toLp 2 (fun p => if p.1 = j then transformedBell U p.2 else 0)

private lemma prepare_inner (j k : J) (U V : Matrix Bool Bool ℂ) :
    inner ℂ (prepare j U) (prepare k V) =
      if j = k then inner ℂ (transformedBell U) (transformedBell V) else 0 := by
  rw [PiLp.inner_apply, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single j]
  · by_cases h : j = k <;> simp [prepare, h, PiLp.inner_apply]
  · intro i _ hi
    simp [prepare, hi]
  · simp

/-- With any one unitary fixed, its preparation code has exactly the original
dimension. The obstruction appears when a common evolution must cover all choices. -/
lemma fixed_unitary_dimension (U : Matrix.unitaryGroup Bool ℂ) :
    Module.finrank ℂ (Submodule.span ℂ (Set.range (fun j : J => prepare j U))) =
      Fintype.card J := by
  apply finrank_span_eq_card
  apply linearIndependent_of_ne_zero_of_inner_eq_zero (𝕜 := ℂ)
  · intro j hz
    have hzero : (U : Matrix Bool Bool ℂ) = 0 := by
      ext t k
      have h := congrArg (fun z : EuclideanSpace ℂ (J × (Bool × Bool)) => z (j, k, t)) hz
      simpa [prepare, transformedBell, ite_mul] using h
    have hu := Matrix.mem_unitaryGroup_iff'.mp U.2
    simp [hzero] at hu
  · intro j k hjk
    rw [prepare_inner, ite_eq_right hjk]

/-- The four actual storage operations, for every original memory basis state,
give a linearly independent family. -/
lemma pauli_preparations_independent :
    LinearIndependent ℂ (fun p : J × (Bool × Bool) => prepare p.1 (pauli p.2)) := by
  apply linearIndependent_of_ne_zero_of_inner_eq_zero (𝕜 := ℂ)
  · rintro ⟨j,a⟩ hz
    have h := prepare_inner j j (pauli a) (pauli a)
    simp only [bell_gram, ite_true] at h
    rw [show prepare j (pauli a) = 0 from hz] at h
    norm_num at h
  · rintro ⟨j,a⟩ ⟨k,b⟩ h
    by_cases hj : j = k <;> simp_all [prepare_inner, bell_gram]

variable (J) in
/-- Common linear domain generated by the actual unitary storage preparations. -/
def preparationSpan : Submodule ℂ (EuclideanSpace ℂ (J × (Bool × Bool))) :=
  Submodule.span ℂ {x | ∃ (j : J) (U : Matrix.unitaryGroup Bool ℂ), x = prepare j U}

/-- Even the four Pauli choices fill the N+2 bit space on taking their common span. -/
lemma preparationSpan_eq_top : preparationSpan J = ⊤ := by
  have hall := (pauli_preparations_independent (J := J)).span_eq_top_of_card_eq_finrank'
    (by rw [finrank_euclideanSpace])
  apply top_unique
  rw [← hall]
  apply Submodule.span_mono
  rintro _ ⟨⟨j,a⟩,rfl⟩
  exact ⟨j, ⟨pauli a, pauli_unitary a⟩, rfl⟩

/-- No single isometry of the common preparation space fits into a final state
space of the original dimension D. Coherence across different storage operations
is the physical assumption that distinguishes this from separate fixed-U codes. -/
lemma no_common_thermalization [Nonempty J] {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℂ F] [FiniteDimensional ℂ F] (hdim : Module.finrank ℂ F = Fintype.card J) :
    IsEmpty (preparationSpan J →ₗᵢ[ℂ] F) := by
  constructor
  intro T
  have h := T.toLinearMap.finrank_le_finrank_of_injective T.injective
  rw [preparationSpan_eq_top, finrank_top, finrank_euclideanSpace, hdim] at h
  simp only [Fintype.card_prod, Fintype.card_bool] at h
  have hp : 0 < Fintype.card J := Fintype.card_pos
  omega

/-- With N = n+1 original bits, the proposed final n-bit hole plus one storage bit
has the original dimension. This is the endpoint counted in AMPS §3.2. -/
theorem mining_memory_no_go (n : ℕ) :
    IsEmpty (preparationSpan (Fin (2 ^ (n + 1))) →ₗᵢ[ℂ]
      EuclideanSpace ℂ (Fin (2 ^ n) × Bool)) := by
  apply no_common_thermalization
  simp [pow_succ]

end AMPS.MiningMemory
