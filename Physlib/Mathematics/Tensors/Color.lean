/-
Copyright (c) 2026 Andrea Pari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrea Pari
-/
module

public import Mathlib.Init
/-!

# Colors of tensor slots

A color is a kind of index with a variance, up or down. Its dual has the same kind and the other
variance.

## i. Overview

A color is the type of an index, made of a kind `κ : K` and a variance, `up` or `down`. A
species (`Species.lean`) assigns a vector space to each color. The kind fixes the basis labels,
and the variance says whether the index is that of a vector (`up`) or a covector (`down`). Lorentz
tensors have one kind, `vec`. The vector `v^μ` has color `⟨vec, up⟩` and the covector `w_μ` has
color `⟨vec, down⟩`.

The slots of a tensor are labelled by colors, not by spaces, so that matching a slot with its
dual is a decidable equality of labels, not an equality of types. The dual of `⟨κ, v⟩` is
`⟨κ, v.dual⟩`, and a contraction such as `v^μ w_μ` pairs a slot of color `c` with a slot of
color `c.dual`.

`Color K` is a structure, rather than the product `K × Variance`, so that `c.dual` works as dot
notation.

## ii. Key results

- `Variance` is the variance of an index, with `Variance.up`, `Variance.down` and
  `Variance.dual`.
- `Color` is a kind of index and a variance.
- `Color.dual` is the dual color, and `Color.dual_dual` proves `c.dual.dual = c` by `rfl`.

## iii. Table of contents

- A. Up and down
- B. Colors

## iv. References

There are no known references for the material in this module.

-/

@[expose] public section

namespace Tensors

/-!

## A. Up and down

`Variance` is two booleans rather than an inductive with two constructors. `dual` swaps them, so
`c.dual.dual` is `c` by `rfl` for a variable color `c`. With an inductive this needs a case split.

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

/-- The dual variance, exchanging up and down. It is an abbrev, so that `simp` and `rw` see
`c.dual.dual` as `c`. -/
abbrev dual (v : Variance) : Variance := ⟨v.isDown, v.isUp, v.ne.symm⟩

end Variance

/-!

## B. Colors

-/

/-- A color `⟨κ, v⟩`, made of a kind of index `κ : K` and its variance `v`. -/
structure Color (K : Type) where
  /-- The kind of index, such as the Lorentz vector index `vec` or a left-handed Weyl index. -/
  kind : K
  /-- Whether the index is up or down. -/
  variance : Variance
deriving DecidableEq

/-- The dual color, with the same kind and the other variance. -/
abbrev Color.dual {K : Type} (c : Color K) : Color K := ⟨c.kind, c.variance.dual⟩

/-- Taking the dual twice gives back the color. -/
lemma Color.dual_dual {K : Type} (c : Color K) : c.dual.dual = c := rfl

end Tensors
