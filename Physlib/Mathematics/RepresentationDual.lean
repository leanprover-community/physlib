/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Mathlib.RepresentationTheory.Basic
public import Mathlib.LinearAlgebra.Dual.Basis
/-!
# Dual representations on a dual basis

## i. Overview

The dual of a representation acts on the dual basis by the transpose of the inverse: if
`ρ g⁻¹` has matrix `M` in a basis, then `ρ.dual g` sends each dual basis vector to the
combination given by the corresponding row of `M`.

## ii. Key results

- `Representation.dual_apply_dualBasis` : the dual representation on a dual basis.

## iii. Table of contents

- A. The dual representation on a dual basis

-/

@[expose] public section

namespace Representation

/-!

## A. The dual representation on a dual basis

-/

/-- The components of a dual representation on a dual basis: if `ρ g⁻¹` has
  matrix `M` in the basis `b` (columns indexing the argument), then `ρ.dual g`
  acts on the dual basis by the rows of `M`. -/
lemma dual_apply_dualBasis {k G V ι : Type*} [CommRing k]
    [Group G] [AddCommGroup V] [Module k V] [Fintype ι] [DecidableEq ι]
    (ρ : Representation k G V) (b : Module.Basis ι k V) (g : G) (i : ι)
    (M : Matrix ι ι k) (hM : ∀ j, ρ g⁻¹ (b j) = ∑ l, M l j • b l) :
    ρ.dual g (b.dualBasis i) = ∑ j, M i j • b.dualBasis j := by
  refine b.ext fun j => ?_
  rw [Representation.dual_apply, Module.Dual.transpose_apply, LinearMap.comp_apply, hM]
  simp [Finsupp.single_apply, Finset.sum_ite_eq, Finset.sum_ite_eq']

end Representation
