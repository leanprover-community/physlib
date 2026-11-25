/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory J. Loges
-/
module

public import Physlib.QuantumMechanics.Operators.Basic
/-!

# Essentially self-adjoint operators

## i. Overview

## ii. Key results

## iii. Table of contents

- A. Definition of ESA
- B. ESA from symmetric or self-adjoint
- C. Properties
  - C.1. Algebraic
  - C.2. Uniqueness of self-adjoint extension

## iv. References

-/

@[expose] public section

namespace LinearPMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-!
## A. Definition of ESA
-/

/-- A LinearPMap is essentially self-adjoint iff its closure is self-adjoint. -/
def IsEssentiallySelfAdjoint (T : H →ₗ.[ℂ] H) : Prop := IsSelfAdjoint T.closure

variable {T : H →ₗ.[ℂ] H}

lemma isEssentiallySelfAdjoint_def :
    T.IsEssentiallySelfAdjoint ↔ IsSelfAdjoint T.closure := Iff.rfl

/-!
## B. ESA from symmetric or self-adjoint
-/

lemma IsSymmetric.isEssentiallySelfAdjoint_iff (h : T.IsSymmetric) (h' : T.HasDenseDomain) :
    T.IsEssentiallySelfAdjoint ↔ T†.domain = T.closure.domain := by
  rw [isEssentiallySelfAdjoint_def, isSelfAdjoint_def,
    (h.isUnbounded_iff_hasDenseDomain.mpr h').adjoint_closure_eq_adjoint]
  constructor <;> intro h''
  · congr
  · exact (eq_of_le_of_domain_eq (h.closure_le_adjoint h') h''.symm).symm

lemma IsSelfAdjoint.isEssentiallySelfAdjoint (h : IsSelfAdjoint T) : T.IsEssentiallySelfAdjoint :=
  isEssentiallySelfAdjoint_def.mpr (h.isClosed.closure_eq.symm ▸ h)

/-!
## C. Properties
-/

namespace IsEssentiallySelfAdjoint

variable (h : T.IsEssentiallySelfAdjoint)

include h

lemma hasDenseDomain : T.HasDenseDomain :=
  hasDenseDomain_iff_closure_hasDenseDomain.mpr h.dense_domain

lemma isSymmetric : T.IsSymmetric := (IsSelfAdjoint.isSymmetric h).of_le T.le_closure

lemma isClosable : T.IsClosable := h.isSymmetric.isClosable h.hasDenseDomain

lemma isUnbounded : T.IsUnbounded :=
  h.isSymmetric.isUnbounded_iff_hasDenseDomain.mpr h.hasDenseDomain

/-!
### C.1. Algebraic
-/

open scoped ComplexConjugate in
@[aesop safe apply]
lemma smul {c : ℂ} (hc : c ≠ 0) (hc' : conj c = c) : (c • T).IsEssentiallySelfAdjoint := by
  simp_all [isEssentiallySelfAdjoint_def, isSelfAdjoint_def, closure_smul _ hc, adjoint_smul _ hc]

@[aesop safe apply]
lemma real_smul {r : ℝ} (hr : r ≠ 0) : (r • T).IsEssentiallySelfAdjoint :=
  h.smul (Complex.ofReal_ne_zero.mpr hr) (Complex.conj_ofReal r)

@[aesop safe apply]
lemma neg : (-T).IsEssentiallySelfAdjoint :=
  neg_eq_neg_one_smul T ▸ h.smul (by norm_num) (by norm_num)

/-!
### C.2. Uniqueness of self-adjoint extension
-/

/-- The closure is the unique self-adjoint extension of an essentially self-adjoint operator. -/
lemma unique_self_adjoint_extension {T₂ : H →ₗ.[ℂ] H} (h_le : T ≤ T₂) (h₂ : IsSelfAdjoint T₂) :
    T₂ = T.closure := by
  have h_cl : T₂.IsClosed := IsSelfAdjoint.isClosed h₂
  have h_le' : T.closure ≤ T₂ := h_cl.closure_eq ▸ h_cl.isClosable.closure_mono h_le
  exact eq_of_le_of_ge (h ▸ h₂ ▸ adjoint_antitone (Or.inl h.hasDenseDomain.closure) h_le') h_le'

end IsEssentiallySelfAdjoint

end LinearPMap
