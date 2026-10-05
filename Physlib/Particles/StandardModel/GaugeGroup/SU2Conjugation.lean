/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith, Nathaneal Sajan
-/
module

public import Physlib.Mathematics.LeviCivita.Basic
public import Physlib.Particles.StandardModel.GaugeGroup.Basic
/-!
# The antisymmetric symbol and complex conjugation in `SU(2)`

`su2Epsilon` is the antisymmetric symbol on two isospin indices: Physlib's `leviCivitaSymbol`
on `Fin 2`, normalized by `su2Epsilon 0 1 = 1`. It transforms by the determinant, so every
`U ∈ SU(2)` fixes it (`sum_su2Epsilon_mul`).

The entrywise conjugate of `U ∈ SU(2)` is `ε U ε⁻¹`, entry by entry `conj U₀₀ = U₁₁`,
`conj U₀₁ = -U₁₀`, `conj U₁₀ = -U₀₁` and `conj U₁₁ = U₀₀`. This is the pseudo-reality of
`SU(2)`. It is a different fact from `conj U = (U⁻¹)ᵀ`, which holds for every unitary `U`. The
classifiers and the Higgs sector use these identities only through explicit re-indexes by `ε`.

- A. The antisymmetric symbol
- B. The entries of an `SU(2)` matrix under conjugation
-/

@[expose] public section

namespace StandardModel

open Matrix ComplexConjugate

/-!

## A. The antisymmetric symbol

-/

/-- The antisymmetric symbol `ε_{ab}` on two `su(2)` fundamental indices: the Levi-Civita
  symbol of `Fin 2`, normalized by `ε 0 1 = 1`. -/
def su2Epsilon (a b : Fin 2) : ℂ := (leviCivitaSymbol ![a, b] : ℤ)

/-- The antisymmetric symbol vanishes when both indices are zero. -/
@[simp] lemma su2Epsilon_zero_zero : su2Epsilon 0 0 = 0 := by
  simp [su2Epsilon, leviCivitaSymbol_eq_zero_of_eq (g := ![0, 0])
    (i := 0) (j := 1) (by decide) rfl]

/-- The antisymmetric symbol on the increasing pair. -/
@[simp] lemma su2Epsilon_zero_one : su2Epsilon 0 1 = 1 := by
  rw [su2Epsilon,
    show (![0, 1] : Fin 2 → Fin 2) = id from funext fun i => by fin_cases i <;> rfl,
    leviCivitaSymbol_id]
  simp

/-- The antisymmetric symbol on the decreasing pair. -/
@[simp] lemma su2Epsilon_one_zero : su2Epsilon 1 0 = -1 := by
  rw [su2Epsilon, show (![1, 0] : Fin 2 → Fin 2) = ⇑(Equiv.swap (0 : Fin 2) 1) from
      funext fun i => by fin_cases i <;> rfl, leviCivitaSymbol_perm,
    Equiv.Perm.sign_swap (by decide)]
  simp

/-- The antisymmetric symbol vanishes when both indices are one. -/
@[simp] lemma su2Epsilon_one_one : su2Epsilon 1 1 = 0 := by
  simp [su2Epsilon, leviCivitaSymbol_eq_zero_of_eq (g := ![1, 1])
    (i := 0) (j := 1) (by decide) rfl]

/-- Every element of `SU(2)` fixes the antisymmetric symbol: contracted against two rows of
  `U` it gives `det U` times itself (`sum_leviCivitaSymbol_mul_prod`), and `det U = 1`. -/
lemma sum_su2Epsilon_mul (U : specialUnitaryGroup (Fin 2) ℂ) (b c : Fin 2) :
    ∑ x : Fin 2, ∑ y : Fin 2, su2Epsilon x y * (U.1 b x * U.1 c y) = su2Epsilon b c := by
  have h := sum_leviCivitaSymbol_mul_prod U.1 ![b, c]
  rw [(mem_specialUnitaryGroup_iff.mp U.2).2, one_mul,
    ← (piFinTwoEquiv fun _ => Fin 2).symm.sum_comp, Fintype.sum_prod_type] at h
  simpa [su2Epsilon, Fin.prod_univ_two, mul_comm, mul_left_comm] using h

/-!

## B. The entries of an `SU(2)` matrix under conjugation

The determinant being one, the adjugate of `U` is its inverse, and `U` being unitary, so is
its conjugate transpose. Reading the adjugate of a `2 × 2` matrix entry by entry gives the four
identities.

-/

/-- The conjugate transpose of an `SU(2)` matrix is its adjugate. -/
lemma su2_star_eq_adjugate (U : specialUnitaryGroup (Fin 2) ℂ) :
    star U.1 = Matrix.adjugate U.1 := by
  have hmem := Matrix.mem_specialUnitaryGroup_iff.mp U.2
  have hu : star U.1 * U.1 = 1 := Matrix.mem_unitaryGroup_iff'.mp hmem.1
  calc star U.1 = star U.1 * (U.1 * Matrix.adjugate U.1) := by
        rw [Matrix.mul_adjugate, hmem.2, one_smul, mul_one]
    _ = star U.1 * U.1 * Matrix.adjugate U.1 := by rw [mul_assoc]
    _ = Matrix.adjugate U.1 := by rw [hu, one_mul]

/-- The conjugate of an entry of an `SU(2)` matrix is the transposed entry of its
  adjugate. -/
lemma su2_conj_apply (U : specialUnitaryGroup (Fin 2) ℂ) (i j : Fin 2) :
    conj (U.1 i j) = Matrix.adjugate U.1 j i := by
  have := congrFun (congrFun (su2_star_eq_adjugate U) j) i
  simpa [Matrix.star_apply] using this

/-- Conjugating the upper left entry of an `SU(2)` matrix gives the lower right one. -/
@[simp] lemma su2_conj_apply_zero_zero (U : specialUnitaryGroup (Fin 2) ℂ) :
    conj (U.1 0 0) = U.1 1 1 := by
  rw [su2_conj_apply, Matrix.adjugate_fin_two]
  simp

/-- Conjugating the lower right entry of an `SU(2)` matrix gives the upper left one. -/
@[simp] lemma su2_conj_apply_one_one (U : specialUnitaryGroup (Fin 2) ℂ) :
    conj (U.1 1 1) = U.1 0 0 := by
  rw [su2_conj_apply, Matrix.adjugate_fin_two]
  simp

/-- Conjugating the upper right entry of an `SU(2)` matrix gives minus the lower left
  one. -/
@[simp] lemma su2_conj_apply_zero_one (U : specialUnitaryGroup (Fin 2) ℂ) :
    conj (U.1 0 1) = -U.1 1 0 := by
  rw [su2_conj_apply, Matrix.adjugate_fin_two]
  simp

/-- Conjugating the lower left entry of an `SU(2)` matrix gives minus the upper right
  one. -/
@[simp] lemma su2_conj_apply_one_zero (U : specialUnitaryGroup (Fin 2) ℂ) :
    conj (U.1 1 0) = -U.1 0 1 := by
  rw [su2_conj_apply, Matrix.adjugate_fin_two]
  simp

end StandardModel
