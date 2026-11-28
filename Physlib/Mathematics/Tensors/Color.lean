/-
Copyright (c) 2026 Andrea Pari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrea Pari
-/
module

public import Mathlib.Init
/-!

# Colors of tensor indices

A color gives the kind of an index of a tensor and whether the index is up or down.

## i. Overview

A color `⟨κ, v⟩` is a kind of index `κ : K` and a variance `v`, `up` or `down`. For Lorentz
tensors there is one kind, `vec`. The vector index of `v^μ` has color `⟨vec, up⟩` and the
covector index of `w_μ` has color `⟨vec, down⟩`.

A tensor has one color per index. A species (`Species.lean`) gives each color a vector space, and a
tensor is an element of the tensor product of the vector spaces of its indices. Each index has a
color rather than a vector space, so that the contraction `S.contr c` (`Species.lean`) pairs `S.V c`
with `S.V c.dual`, and an equation of written-out colors holds by `rfl`. When two colors are equal
only through a proof, vectors are moved between their vector spaces by `S.cast` (`Species.lean`,
§C).

The dual of `⟨κ, v⟩` is `⟨κ, v.dual⟩`, the same kind with the other variance. A contraction such
as `v^μ w_μ` pairs an index of color `c` with an index of color `c.dual`. `Color K` is a structure
rather than the product `K × Variance`, so that a written-out color `⟨κ, up⟩` has the type
`Color K` and `⟨κ, up⟩.dual` works as dot notation.

## ii. Key results

- `Variance` : the variance of an index, with `Variance.up`, `Variance.down` and
  `Variance.dual`.
- `Color` : a kind of index and a variance.
- `Color.dual` : the dual color, and `Color.dual_dual` : `c.dual.dual = c` by `rfl`.
- `Color.dual_mk`, `Variance.dual_up`, `Variance.dual_down` : `simp` computes the dual of a
  written-out color, `⟨κ, up⟩.dual = ⟨κ, down⟩`.

## iii. Table of contents

- A. Variance
- B. Colors

## iv. References

There are no known references for the material in this module.

-/

@[expose] public section

namespace Tensor

/-!

## A. Variance

`Variance` is two booleans, and `dual` swaps them. So `c.dual.dual` is `c` by definition, also for
a variable color `c`, and the vector spaces `S.V c.dual.dual` and `S.V c` of a species are the same
type.

-/

/-- The variance of an index, up (contravariant, `v^μ`) or down (covariant, `w_μ`). -/
structure Variance where
  /-- Whether the index is up. -/
  isUp : Bool
  /-- Whether the index is down. -/
  isDown : Bool
  /-- An index is either up or down. -/
  ne : isUp ≠ isDown
deriving DecidableEq

namespace Variance

/-- An upper index, as in `v^μ`. -/
@[match_pattern]
abbrev up : Variance := ⟨true, false, by decide⟩

/-- A lower index, as in `w_μ`. -/
@[match_pattern]
abbrev down : Variance := ⟨false, true, by decide⟩

/-- The dual variance, exchanging up and down. It is reducible, as is `Color.dual`, so that instance
search and unification see `⟨κ, up⟩.dual` as `⟨κ, down⟩` and `c.dual.dual` as `c`. -/
abbrev dual (v : Variance) : Variance := ⟨v.isDown, v.isUp, v.ne.symm⟩

/-- The dual of an upper index is a lower index. -/
@[simp]
lemma dual_up : up.dual = down := rfl

/-- The dual of a lower index is an upper index. -/
@[simp]
lemma dual_down : down.dual = up := rfl

end Variance

/-!

## B. Colors

-/

/-- A color `⟨κ, v⟩`, made of a kind of index `κ : K` and its variance `v`. -/
structure Color (K : Type) where
  /-- The kind of index, such as a Lorentz vector index or a left-handed Weyl spinor index. -/
  kind : K
  /-- Whether the index is up or down. -/
  variance : Variance
deriving DecidableEq

/-- The dual color, with the same kind and the other variance. It is reducible, as is
`Variance.dual`, so that instance search and unification see `⟨κ, up⟩.dual` as `⟨κ, down⟩`. -/
abbrev Color.dual {K : Type} (c : Color K) : Color K := ⟨c.kind, c.variance.dual⟩

/-- Taking the dual twice gives back the color. -/
lemma Color.dual_dual {K : Type} (c : Color K) : c.dual.dual = c := rfl

/-- The dual of `⟨κ, v⟩` is `⟨κ, v.dual⟩`. With `Variance.dual_up` and `Variance.dual_down`,
`simp` computes the dual of a written-out color, `⟨κ, up⟩.dual = ⟨κ, down⟩`. -/
@[simp]
lemma Color.dual_mk {K : Type} (κ : K) (v : Variance) :
    (⟨κ, v⟩ : Color K).dual = ⟨κ, v.dual⟩ := rfl

end Tensor
