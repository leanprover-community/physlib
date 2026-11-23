/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import Mathlib.RepresentationTheory.Basic
/-!
# Dual representations on a dual basis

The dual of a representation on a dual basis, and the range of a linear map out of a dual space.

## i. Overview

The dual of a representation acts on the dual basis by the transpose of the inverse. If
`ρ g⁻¹` has matrix `M` in a basis, then `ρ.dual g` sends each dual basis vector to the
combination given by the corresponding row of `M`.

A linear map out of the dual of a finite-dimensional space is determined by its values on the
coordinate functionals of a basis, so its range is the join of the lines through those values.

## ii. Key results

- `Representation.dual_apply_dualBasis` : the dual representation on a dual basis.
- `LinearMap.range_eq_iSup_span_coord` : the range of a map out of a dual space as a join of
  lines.

## iii. Table of contents

- A. The dual representation on a dual basis
- B. Maps out of a dual space

## iv. References

* None.

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

namespace LinearMap

/-!

## B. Maps out of a dual space

-/

/-- The range of a linear map out of the dual of a space with a finite basis is the join of the
  lines through its values on the coordinate functionals of the basis. -/
lemma range_eq_iSup_span_coord {k V M ι : Type*} [CommRing k] [AddCommGroup V] [Module k V]
    [AddCommGroup M] [Module k M] [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι k V) (f : Module.Dual k V →ₗ[k] M) :
    LinearMap.range f = ⨆ j, Submodule.span k {f (b.coord j)} := by
  rw [LinearMap.range_eq_map, ← b.dualBasis.span_eq, Submodule.map_span, ← Set.range_comp]
  rw [show (⇑f ∘ ⇑b.dualBasis) = fun j => f (b.coord j) from funext fun j => by
    simp [Module.Basis.coe_dualBasis]]
  rw [Submodule.span_range_eq_iSup]

end LinearMap
