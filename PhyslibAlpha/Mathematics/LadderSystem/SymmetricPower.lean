/-
Copyright (c) 2026 Tom Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Diem
-/
module

public import PhyslibAlpha.Mathematics.LadderSystem.OccupationBasis
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
/-!

# The excitation sector is the symmetric power

The excitation-number sector `vacuumSpan L Ω n` is linearly isomorphic to `Sym^n(K^d)`.

## i. Overview

`vacuumSpan L Ω n` is linearly isomorphic to the `n`-th symmetric power of `K^d` -- concretely, to
the free `K`-vector space on `Sym (Fin d) n` (Mathlib's own type of size-`n` multisets on `Fin d`,
the standard combinatorial model of `Sym^n(K^d)`'s natural basis once a basis `e_1,…,e_d` of `K^d`
is fixed: a multiset `{i_1,…,i_n}` names the basis vector `e_{i_1} ⊙ ⋯ ⊙ e_{i_n}`). The
isomorphism sends this basis to the occupation-number states, i.e. it is exactly
`OccupationBasis.lean`'s `vacuumBasis` reindexed along `countFunEquivSym`.

## ii. Key results

- `LadderSystem.vacuumSpanSymEquiv` : `(Sym (Fin d) n →₀ K) ≃ₗ[K] vacuumSpan L Ω n`.
- `LadderSystem.vacuumSpanSymEquiv_single` : the basis vector of a multiset is sent to the
  occupation-number state of its count function.

## iii. Table of contents

- A. The isomorphism with the symmetric power
- B. The image of the basis vectors

## iv. References

* None.
-/

@[expose] public section

open Module (Basis)

namespace LadderSystem

variable {K V : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V] {d : ℕ}
    (L : LadderSystem K V d)

/-!

## A. The isomorphism with the symmetric power

-/

/-- `vacuumSpan L Ω n` is linearly isomorphic to `Sym^n(K^d)` (realized as the free `K`-module
on `Sym (Fin d) n`), matching the natural monomial-type basis on one side to the occupation-number
basis on the other. -/
noncomputable def vacuumSpanSymEquiv {Ω : V} (P : L.HasVacuum Ω) (n : ℕ) :
    (Sym (Fin d) n →₀ K) ≃ₗ[K] L.vacuumSpan Ω n :=
  Finsupp.basisSingleOne.equiv (vacuumBasis L P n) (countFunEquivSym d n).symm

/-!

## B. The image of the basis vectors

-/

/-- The isomorphism sends the basis vector for multiset `s` to the occupation-number state with
that multiset's count function. -/
lemma vacuumSpanSymEquiv_single {Ω : V} (P : L.HasVacuum Ω) (n : ℕ) (s : Sym (Fin d) n) :
    (L.vacuumSpanSymEquiv P n (Finsupp.single s 1) : V)
      = L.word (countWord d ((countFunEquivSym d n).symm s).1) Ω := by
  have h := Basis.equiv_apply (b := (Finsupp.basisSingleOne : Basis (Sym (Fin d) n) K _))
    (b' := vacuumBasis L P n) (e := (countFunEquivSym d n).symm) s
  rw [Finsupp.coe_basisSingleOne] at h
  have heq : L.vacuumSpanSymEquiv P n (Finsupp.single s 1)
      = vacuumBasis L P n ((countFunEquivSym d n).symm s) := h
  rw [heq, vacuumBasis_apply]

end LadderSystem
