/-
Copyright (c) 2026 Giuseppe Sorge. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuseppe Sorge
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.CrossProduct
/-!

# The cross product of three-dimensional vectors

Identities for the cross product `⨯₃` on `Fin 3 → ℝ`, beyond those already in Mathlib, used in the
formalisation of rigid-body dynamics.

-/

@[expose] public section

namespace Matrix

/-- The component form of the triple cross product `v ⨯₃ (w ⨯₃ v)`: by the `bac−cab` identity its
`i`-th entry is `|v|² wᵢ − (v · w) vᵢ`, written with the explicit component sums `∑ k, (v k)²` and
`∑ j, v j * w j`. -/
lemma cross_cross_self_apply (v w : Fin 3 → ℝ) (i : Fin 3) :
    (v ⨯₃ (w ⨯₃ v)) i = (∑ k, (v k) ^ 2) * w i - (∑ j, v j * w j) * v i := by
  rw [cross_cross_eq_smul_sub_smul']
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, dotProduct, Fin.sum_univ_three]
  ring

/-- Contracting `w` with the triple cross product `v ⨯₃ (w ⨯₃ v)` gives `(w ⨯₃ v) ⬝ᵥ (w ⨯₃ v)`
(over `ℝ`, the squared length `|w × v|²`), by two cyclic permutations of the scalar triple
product. -/
lemma dotProduct_cross_cross_self {R : Type*} [CommRing R] (v w : Fin 3 → R) :
    w ⬝ᵥ (v ⨯₃ (w ⨯₃ v)) = (w ⨯₃ v) ⬝ᵥ (w ⨯₃ v) := by
  rw [triple_product_permutation, triple_product_permutation]

/-- The squared length `(ω ⨯₃ v) ⬝ᵥ (ω ⨯₃ v)` of the cross product with a fixed vector `ω` is a
smooth function of `v`. -/
lemma contDiff_cross_dotProduct_cross (ω : Fin 3 → ℝ) :
    ContDiff ℝ ⊤ fun v : Fin 3 → ℝ => (ω ⨯₃ v) ⬝ᵥ (ω ⨯₃ v) := by
  simp only [dotProduct, Fin.sum_univ_three, cross_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  fun_prop

end Matrix
