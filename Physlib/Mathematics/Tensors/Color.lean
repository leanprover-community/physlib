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
covector index of `w_μ` has color `⟨vec, down⟩`. Complex Lorentz tensors have three kinds, one
for each of the two types of Weyl spinor index and one for the vector index.

A tensor has one color per index. A species (`Species.lean`) gives each color a space, and a
tensor is an element of the tensor product of the spaces of its indices. Each index has a color
rather than a space, so that whether two indices can be contracted is an equation of colors,
`c j = (c i).dual`, which Lean checks by computation when the colors are known. When two colors
are equal only through a proof, vectors are moved between their spaces by `S.cast`
(`Species.lean`, §C).

The dual of `⟨κ, v⟩` is `⟨κ, v.dual⟩`, the same kind with the other variance. A contraction such
as `v^μ w_μ` pairs an index of color `c` with an index of color `c.dual`. `Color K` is a structure
rather than the product `K × Variance`, so that `c.dual` works as dot notation.

## ii. Key results

- `Variance` : the variance of an index, with `Variance.up`, `Variance.down` and
  `Variance.dual`.
- `Color` : a kind of index and a variance.
- `Color.dual` : the dual color, and `Color.dual_dual` : `c.dual.dual = c` by `rfl`.

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
a variable color `c`, and the spaces `S.V c.dual.dual` and `S.V c` of a species are the same type.

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
  /-- The kind of index, such as a Lorentz vector index or a left-handed Weyl spinor index. -/
  kind : K
  /-- Whether the index is up or down. -/
  variance : Variance
deriving DecidableEq

/-- The dual color, with the same kind and the other variance. -/
abbrev Color.dual {K : Type} (c : Color K) : Color K := ⟨c.kind, c.variance.dual⟩

/-- Taking the dual twice gives back the color. -/
lemma Color.dual_dual {K : Type} (c : Color K) : c.dual.dual = c := rfl

end Tensor
