/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.LorentzGroup.Basic
public import PhyslibAlpha.Relativity.MinkowskiMatrix
/-!
# The defining relation of the Lorentz group on its entries

The relation `Λ η Λᵀ = η` over `ℂ`, read on a single entry and with integer metric entries.

## i. Overview

`Physlib.Relativity.LorentzGroup.Basic` states the defining relation of the Lorentz group as
the matrix equation `Λ η Λᵀ = η` over `ℝ`. A classification of invariant tensors contracts
that relation one metric pairing at a time, over `ℂ` and against entries which a decision
procedure has to evaluate. `sum_minkowskiMatrixZ_mul` is the relation in exactly that form:
the entry `(a, b)`, the coefficients cast into `ℂ`, and the metric entries taken from
`minkowskiMatrixZ` rather than `minkowskiMatrix`.

## ii. Key results

- `LorentzGroup.sum_minkowskiMatrixZ_mul` : the defining relation on the entry `(a, b)`, over
  `ℂ` and with integer metric entries.

## iii. Table of contents

- A. The defining relation on an entry

## iv. References

The defining relation and its matrix forms are in `Physlib.Relativity.LorentzGroup.Basic`.

-/

@[expose] public section

noncomputable section

open Matrix
open Complex

namespace LorentzGroup

open minkowskiMatrix

variable {d : ℕ}

/-!

## A. The defining relation on an entry

-/

/-- The defining relation `Λ η Λᵀ = η` over `ℂ`, read on the entry `(a, b)` and with the
  integer Minkowski matrix in place of `minkowskiMatrix`. This is the form the invariant
  classifications contract against, one metric pairing per pair of slots. -/
lemma sum_minkowskiMatrixZ_mul (Λ : LorentzGroup d) (a b : Fin 1 ⊕ Fin d) :
    ∑ x : Fin 1 ⊕ Fin d, ∑ y : Fin 1 ⊕ Fin d, ((minkowskiMatrixZ x y : ℤ) : ℂ)
        * (((Λ.1 a x : ℝ) : ℂ) * ((Λ.1 b y : ℝ) : ℂ))
      = ((minkowskiMatrixZ a b : ℤ) : ℂ) := by
  have hR : ∑ x : Fin 1 ⊕ Fin d, ∑ y : Fin 1 ⊕ Fin d,
      ((minkowskiMatrixZ x y : ℤ) : ℝ) * (Λ.1 a x * Λ.1 b y)
        = ((minkowskiMatrixZ a b : ℤ) : ℝ) := by
    have h := congrFun (congrFun
      (mul_minkowskiMatrix_mul_transpose (Λ := Λ)) a) b
    simp only [Matrix.mul_apply, Matrix.transpose_apply] at h
    rw [minkowskiMatrixZ.cast_apply, ← h, Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun x _ => by rw [minkowskiMatrixZ.cast_apply]; ring
  simpa only [map_sum, map_mul, Complex.ofRealHom_eq_coe, Complex.ofReal_intCast] using
    congrArg Complex.ofRealHom hR

end LorentzGroup

end
