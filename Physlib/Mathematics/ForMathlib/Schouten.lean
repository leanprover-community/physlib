/-
Copyright (c) 2026 Andrea Pari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrea Pari
-/
module

public import Mathlib.LinearAlgebra.SesquilinearForm.Basic
import Mathlib.Tactic.LinearCombination

/-!

# The Schouten identity

An alternating bilinear form on a module with a basis of two vectors satisfies the Schouten
identity.

## i. Overview

For an alternating bilinear form `B` on a module with a basis of two vectors,
`B(u, v) w + B(v, w) u + B(w, u) v = 0` for all `u`, `v`, `w`. Expanding each vector in the basis,
`B` vanishes on equal basis vectors and is antisymmetric on the other two, so the sum cancels.
Read at a label on three basis vectors, it relates the entries of the matrix of `B`.

## ii. Key results

- `LinearMap.IsAlt.schouten` : the Schouten identity for an alternating form in two dimensions.
- `LinearMap.IsAlt.schouten_basis` : the same on basis vectors, read at a label.

## iii. Table of contents

- A. Alternating forms in two dimensions

## iv. References

* None.

-/

@[expose] public section

open Module

/-!

## A. Alternating forms in two dimensions

-/

namespace LinearMap.IsAlt

variable {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Fintype ι]
  [DecidableEq ι] {B : LinearMap.BilinForm R M}

/-- The Schouten identity, `B(u, v) w + B(v, w) u + B(w, u) v = 0`, for an alternating bilinear
form on a module with a basis of two vectors. -/
lemma schouten (hB : LinearMap.IsAlt B) (b : Basis ι R M) (h2 : Fintype.card ι = 2) (u v w : M) :
    B u v • w + B v w • u + B w u • v = 0 := by
  obtain ⟨i, j, hij, huniv⟩ := Finset.card_eq_two.mp (h2 : Finset.univ.card = 2)
  -- Each vector is `x^i e_i + x^j e_j`, and `B` vanishes on `e_i, e_i` and on `e_j, e_j`.
  have hexp (x : M) : x = b.repr x i • b i + b.repr x j • b j := by
    conv_lhs => rw [← b.sum_repr x, huniv, Finset.sum_pair hij]
  rw [hexp u, hexp v, hexp w]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    LinearMap.IsAlt.self_eq_zero hB, (LinearMap.IsAlt.neg hB (b i) (b j)).symm]
  module

/-- The Schouten identity on the basis vectors `e_i`, `e_j` and `e_k`, read at the label `l`,
`B(e_i, e_j) δ_lk = B(e_i, e_k) δ_jl - B(e_j, e_k) δ_il`. -/
lemma schouten_basis (hB : LinearMap.IsAlt B) (b : Basis ι R M) (h2 : Fintype.card ι = 2)
    (i j k l : ι) :
    B (b i) (b j) * (if l = k then 1 else 0) =
      B (b i) (b k) * (if j = l then 1 else 0) - B (b j) (b k) * (if i = l then 1 else 0) := by
  have h := congrArg (fun x => b.repr x l) (hB.schouten b h2 (b i) (b j) (b k))
  simp only [map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply, Basis.repr_self,
    Finsupp.single_apply, smul_eq_mul, map_zero, Finsupp.zero_apply, @eq_comm _ k l] at h
  linear_combination h + (if j = l then 1 else 0) * LinearMap.IsAlt.neg hB (b k) (b i)

end LinearMap.IsAlt
