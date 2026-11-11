/-
Copyright (c) 2026 Andrea Pari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrea Pari
-/
module

public import Mathlib.LinearAlgebra.SesquilinearForm.Basic

/-!

# The Schouten identity

An alternating bilinear form on a module with a basis of two vectors satisfies the Schouten
identity.

## i. Overview

For an alternating bilinear form `B` on a module with a basis of two vectors,
`B(u, v) w + B(v, w) u + B(w, u) v = 0` for all `u`, `v`, `w`. Expanding each vector in the basis,
`B` vanishes on equal basis vectors and is antisymmetric on the other two, so the sum cancels.

## ii. Key results

- `LinearMap.IsAlt.schouten` : the Schouten identity for an alternating form in two dimensions.

## iii. Table of contents

- A. Alternating forms in two dimensions

## iv. References

There are no known references for the material in this module.

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

end LinearMap.IsAlt
