/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann, Gregory J. Loges
-/
module

public import Physlib.QuantumMechanics.Operators.Basic
/-!

# Self-adjoint operators

## i. Overview

The purpose of this module is to collect basic properties of self-adjoint operators.

See `LinearPMap.instStar` and `LinearPMap.isSelfAdjoint_def` for the definition of `IsSelfAdjoint`
for `LinearPMap`s.

## ii. Key results

## iii. Table of contents

- A. Self-adjoint from symmetric
- B. Properties

## iv. References

-/

@[expose] public section

namespace LinearPMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {T : H →ₗ.[ℂ] H}

/-!
## A. Self-adjoint from symmetric
-/

/-- A densely-defined symmetric operators is self-adjoint *if and only if*
it has the same domain as its adjoint. -/
lemma IsSymmetric.isSelfAdjoint_iff (h : T.IsSymmetric) (h' : T.HasDenseDomain) :
    IsSelfAdjoint T ↔ T†.domain = T.domain := by
  constructor <;> intro h''
  · congr
  · exact (eq_of_le_of_domain_eq ((isSymmetric_iff_le_adjoint h').mp h) h''.symm).symm

open Complex InnerProductSpace in
/-- Self-adjointness from surjectivity of `T ± i`: a symmetric, densely-defined operator `T` for
which `T + I • 1` and `T - I • 1` both have full range is self-adjoint. -/
lemma IsSymmetric.isSelfAdjoint_of_range_eq_top (hsym : T.IsSymmetric) (hdense : T.HasDenseDomain)
    (hadd : (T + I • 1).toFun.range = ⊤) (hsub : (T - I • 1).toFun.range = ⊤) :
    IsSelfAdjoint T := by
  have hplus : ∀ φ : H, ∃ ψ : T.domain, T ψ + I • (ψ : H) = φ := fun φ => by
    obtain ⟨ψ, hψ⟩ := LinearMap.range_eq_top.mp hadd φ
    exact ⟨⟨(ψ : H), (Submodule.mem_inf.mp ψ.2).1⟩, hψ⟩
  have hminus : ∀ φ : H, ∃ ψ : T.domain, T ψ - I • (ψ : H) = φ := fun φ => by
    obtain ⟨ψ, hψ⟩ := LinearMap.range_eq_top.mp hsub φ
    exact ⟨⟨(ψ : H), (Submodule.mem_inf.mp ψ.2).1⟩, hψ⟩
  rw [isSelfAdjoint_def]
  have hle : T ≤ T.adjoint := (isSymmetric_def.mp hsym).le_adjoint hdense
  apply le_antisymm _ hle
  apply le_of_eqLocus_ge
  intro w hw
  let W : T.adjoint.domain := ⟨w, hw⟩
  obtain ⟨x, hx⟩ := hminus (T.adjoint W - I • (W : H))
  set X : T.adjoint.domain := ⟨x, hle.1 x.2⟩ with hX
  have hxeq : T.adjoint X = T x := (hle.2 (x := x) (y := X) rfl).symm
  have hdiff : T.adjoint (W - X) = I • ((W - X) : H) := by
    rw [LinearPMap.map_sub, hxeq, hX, Subtype.coe_mk, smul_sub, sub_eq_sub_iff_sub_eq_sub, hx]
  have hker : ∀ w : T.adjoint.domain, T.adjoint w = I • (w : H) → (w : H) = 0 := by
    intro w hw
    obtain ⟨v, hv⟩ := hplus (w : H)
    suffices ⟪↑w, T v + I • v⟫_ℂ = 0 by
      exact inner_self_eq_zero.mp (hv ▸ this)
    rw [inner_add_right, inner_smul_right, ← adjoint_isFormalAdjoint hdense w v, hw,
      inner_smul_left, conj_I]
    ring
  obtain rfl : w = (x : H) := sub_eq_zero.mp (hker (W - X) hdiff)
  exact ⟨hw, x.2, hxeq⟩

/-!
## B. Properties
-/

namespace IsSelfAdjoint

variable (h : IsSelfAdjoint T)

include h

/-- A self-adjoint operator is symmetric. -/
lemma isSymmetric : T.IsSymmetric := by
  rw [isSymmetric_def]
  nth_rw 1 [← h]
  exact adjoint_isFormalAdjoint h.dense_domain

/-- A self-adjoint operator is closable. -/
lemma isClosable : T.IsClosable := h.isClosed.isClosable

/-- A self-adjoint operator is unbounded (densely defined and closable). -/
lemma isUnbounded : T.IsUnbounded := ⟨h.dense_domain, isClosable h⟩

/-- The adjoint of a self-adjoint operator is self-adjoint. -/
@[aesop safe apply]
protected lemma adjoint : IsSelfAdjoint T† := by simp_all only [isSelfAdjoint_def]

open scoped ComplexConjugate in
@[aesop safe apply]
protected lemma smul {c : ℂ} (hc : c ≠ 0) (hc' : conj c = c) : IsSelfAdjoint (c • T) := by
  rw [isSelfAdjoint_def, T.adjoint_smul hc, hc', isSelfAdjoint_def.mp h]

@[aesop safe apply]
protected lemma real_smul {r : ℝ} (hr : r ≠ 0) : IsSelfAdjoint (r • T) :=
  IsSelfAdjoint.smul h (Complex.ofReal_ne_zero.mpr hr) (Complex.conj_ofReal r)

@[aesop safe apply]
protected lemma neg : IsSelfAdjoint (-T) :=
  neg_eq_neg_one_smul T ▸ IsSelfAdjoint.smul h (by norm_num) (by norm_num)

end IsSelfAdjoint

end LinearPMap
