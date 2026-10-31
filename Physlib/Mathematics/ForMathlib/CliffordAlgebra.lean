/-
Copyright (c) 2026 Philippe Kevorkian. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philippe Kevorkian
-/
module

public import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis

/-!

# The dimension of exterior and Clifford algebras

## i. Overview

Over a field, the exterior algebra of a vector space of dimension `n` has dimension `2 ^ n`: a
basis of the space indexed by `Fin n` gives a basis of the exterior algebra indexed by the subsets
of `Fin n`. When `2` is invertible, the Clifford algebra of any quadratic form on the space is
linearly equivalent to the exterior algebra (`CliffordAlgebra.equivExterior`), so it has the same
dimension.

## ii. Key results

- `ExteriorAlgebra.finrank_eq_two_pow` : the exterior algebra has dimension `2 ^ n`.
- `CliffordAlgebra.finrank_eq_two_pow` : the Clifford algebra has dimension `2 ^ n`.

## iii. Table of contents

- A. The exterior algebra
- B. The Clifford algebra

## iv. References

There are no known references for the material in this module.

-/

@[expose] public section

/-! ## A. The exterior algebra -/

namespace ExteriorAlgebra

/-- The exterior algebra of a finite-dimensional vector space `V` has dimension
`2 ^ finrank K V`. -/
lemma finrank_eq_two_pow (K V : Type*) [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] :
    Module.finrank K (ExteriorAlgebra K V) = 2 ^ Module.finrank K V := by
  rw [Module.finrank_eq_card_basis (Module.finBasis K V).ExteriorAlgebra, Fintype.card_finset,
    Fintype.card_fin]

end ExteriorAlgebra

/-! ## B. The Clifford algebra -/

namespace CliffordAlgebra

/-- When `2` is invertible, the Clifford algebra of a quadratic form on a finite-dimensional vector
space `V` has dimension `2 ^ finrank K V`, as the exterior algebra of `V`. -/
lemma finrank_eq_two_pow {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Invertible (2 : K)] (Q : QuadraticForm K V) :
    Module.finrank K (CliffordAlgebra Q) = 2 ^ Module.finrank K V := by
  rw [(equivExterior Q).finrank_eq, ExteriorAlgebra.finrank_eq_two_pow]

end CliffordAlgebra
