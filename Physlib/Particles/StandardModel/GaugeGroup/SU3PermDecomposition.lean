/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.LinearAlgebra.Matrix.Permutation
/-!
# The `SU(3)` Weyl group

## i. Overview

The cyclic colour rotation

  `su3Perm = !![0, 0, 1; 1, 0, 0; 0, 1, 0]`

sends a colour triplet `(a, b, c)` to `(c, a, b)`, cycling the three colours and so cycling
the three colour weights that the first two coordinates of a `GaugeWeight` record.
`gaugeSU3Perm` is its image in the gauge group.

`su3Perm` is the lift to `SU(3)` of a three-cycle in the Weyl group `S₃`. A three-cycle is
an even permutation, so its permutation matrix already has determinant `1`: unlike the
`SU(2)` transposition, which has to be twisted by a sign to land in `SU(2)`, the cyclic
matrix needs no phase correction at all.

The three-cycle generates only the alternating subgroup `A₃` of the Weyl group `S₃` of
`SU(3)`. The whole of `S₃` is available here too: `su3Weyl` sends a permutation `σ` to its
permutation matrix scaled by the sign of `σ`, which lands in `SU(3)` because the dimension
is odd, and is a group homomorphism because both factors are multiplicative. It is
injective, so `S₃` sits inside `SU(3)` as a genuine subgroup — a point on which `SU(3)`
differs from `SU(2)`, whose Weyl group lifts only to an element of order four.
`su3Transp = !![0, -1, 0; -1, 0, 0; 0, 0, -1]` is the lift of the transposition `(0 1)`; it
squares to `1`, and `t c t = c⁻¹` for `c` the three-cycle.

`su3Perm` cubes to `1`, so it has order three in `SU(3)`, and its spectrum is contained in
the cube roots of unity: `su3PermSign` is the character `k ↦ ω ^ k` on `ZMod 3` for
`ω = su3Omega = exp (2 π i / 3)`, attaching the eigenvalue to each grade.

## ii. Key results

- `su3Perm` : the `SU(3)` cyclic Weyl element `!![0, 0, 1; 1, 0, 0; 0, 1, 0]`, and
  `gaugeSU3Perm` its image in the gauge group.
- `su3Weyl` : the Weyl group `S₃` as a subgroup of `SU(3)`, with `su3Transp` the lift of a
  transposition and `gaugeSU3Weyl` the version landing in the gauge group.
- `su3Omega` : the primitive cube root of unity `exp (2 π i / 3)`.
- `su3PermSign` : the character `k ↦ ω ^ k` on `ZMod 3`, injective and multiplicative.

## iii. Table of contents

- A. The `SU(3)` cyclic Weyl element
- B. The Weyl group `S₃` inside `SU(3)`
- C. The cube-root character of `ZMod 3`

-/
@[expose] public section

namespace StandardModel

open Matrix

/-!

## A. The `SU(3)` cyclic Weyl element

-/

/-- The `SU(3)` cyclic permutation element `!![0, 0, 1; 1, 0, 0; 0, 1, 0]`. On a colour
  triplet it sends `(a, b, c)` to `(c, a, b)`, cycling the three colours; it cubes to `1`,
  so it has order three in `SU(3)`. A three-cycle is even, so the plain permutation matrix
  already has determinant `1`. -/
noncomputable def su3Perm : specialUnitaryGroup (Fin 3) ℂ :=
  ⟨!![0, 0, 1; 1, 0, 0; 0, 1, 0], by
    rw [Matrix.mem_specialUnitaryGroup_iff]
    refine ⟨?_, ?_⟩
    · rw [Matrix.mem_unitaryGroup_iff]
      ext a b
      fin_cases a <;> fin_cases b <;>
        simp [Matrix.mul_apply, Fin.sum_univ_three, star_eq_conjTranspose,
          Matrix.conjTranspose_apply]
    · simp [Matrix.det_fin_three]⟩

/-- The underlying matrix of the cyclic element. -/
lemma su3Perm_coe :
    (su3Perm : specialUnitaryGroup (Fin 3) ℂ).1 = !![0, 0, 1; 1, 0, 0; 0, 1, 0] := rfl

/-- The inverse cyclic element is the transpose `!![0, 1, 0; 0, 0, 1; 1, 0, 0]`, the
  three-cycle running the other way. -/
lemma su3Perm_inv_coe :
    (su3Perm⁻¹ : specialUnitaryGroup (Fin 3) ℂ).1 = !![0, 1, 0; 0, 0, 1; 1, 0, 0] := by
  rw [← Matrix.star_eq_inv, Matrix.specialUnitaryGroup.coe_star, su3Perm_coe]
  ext a b
  fin_cases a <;> fin_cases b <;> simp

/-- The cyclic element cubes to the identity, so it has order three in `SU(3)`. This is why
  the grading group below is `ZMod 3`. -/
lemma su3Perm_pow_three : su3Perm ^ 3 = 1 := by
  ext a b
  rw [SubmonoidClass.coe_pow, su3Perm_coe]
  fin_cases a <;> fin_cases b <;>
    simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_three]

/-- The cyclic element as a gauge transformation: trivial on isospin and hypercharge. -/
noncomputable def gaugeSU3Perm : GaugeGroupI := ⟨su3Perm, 1, 1⟩

/-!

## B. The Weyl group `S₃` inside `SU(3)`

-/

/-- The Weyl group `S₃` of `SU(3)`, lifted into `SU(3)` itself: a permutation `σ` goes to
  its permutation matrix scaled by the sign of `σ`. Both factors are multiplicative in `σ`,
  so this is a group homomorphism, and the determinant comes out right because the dimension
  is odd — scaling a `3 × 3` matrix by `-1` multiplies its determinant by `-1`, cancelling
  the determinant of an odd permutation matrix. No such lift exists for `SU(2)`, where the
  Weyl group reaches only an element of order four. -/
noncomputable def su3Weyl : Equiv.Perm (Fin 3) →* specialUnitaryGroup (Fin 3) ℂ where
  toFun σ := ⟨((Equiv.Perm.sign σ : ℤ) : ℂ) • Matrix.permMatrixHom σ, by
    have hs : ((Equiv.Perm.sign σ : ℤ) : ℂ) * ((Equiv.Perm.sign σ : ℤ) : ℂ) = 1 := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> rw [h] <;> norm_num
    have hstar : (Matrix.permMatrixHom σ : Matrix (Fin 3) (Fin 3) ℂ)ᴴ
        = Matrix.permMatrixHom σ⁻¹ := by
      simp [Matrix.permMatrixHom_apply]
    rw [Matrix.mem_specialUnitaryGroup_iff]
    refine ⟨?_, ?_⟩
    · rw [Matrix.mem_unitaryGroup_iff, star_eq_conjTranspose, Matrix.conjTranspose_smul,
        star_intCast, hstar, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hs, one_smul,
        ← map_mul, mul_inv_cancel, map_one]
    · rw [Matrix.det_smul, Matrix.permMatrixHom_apply, Matrix.det_permutation,
        Equiv.Perm.sign_inv, Fintype.card_fin]
      have h4 : ((Equiv.Perm.sign σ : ℤ) : ℂ) ^ 3 * ((Equiv.Perm.sign σ : ℤ) : ℂ)
          = (((Equiv.Perm.sign σ : ℤ) : ℂ) * ((Equiv.Perm.sign σ : ℤ) : ℂ))
            * (((Equiv.Perm.sign σ : ℤ) : ℂ) * ((Equiv.Perm.sign σ : ℤ) : ℂ)) := by ring
      rw [h4, hs, one_mul]⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' σ τ := by apply Subtype.ext; simp [smul_smul, mul_comm]

/-- The matrix of the lift of a permutation. -/
lemma su3Weyl_coe (σ : Equiv.Perm (Fin 3)) :
    (su3Weyl σ : specialUnitaryGroup (Fin 3) ℂ).1
      = ((Equiv.Perm.sign σ : ℤ) : ℂ) • Matrix.permMatrixHom σ := rfl

/-- The lift is injective, so the Weyl group `S₃` is a genuine subgroup of `SU(3)`. A
  permutation whose lift is the identity fixes every index, because the diagonal entry at
  `i` of the lift is a nonzero sign when `σ` fixes `i` and is `0` otherwise. -/
lemma su3Weyl_injective : Function.Injective su3Weyl := by
  refine (injective_iff_map_eq_one su3Weyl).mpr fun σ hσ => ?_
  have h := Subtype.ext_iff.mp hσ
  simp only [su3Weyl_coe, Matrix.permMatrixHom_apply, OneMemClass.coe_one] at h
  have hs : ((Equiv.Perm.sign σ : ℤ) : ℂ) ≠ 0 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hσ' | hσ' <;> rw [hσ'] <;> norm_num
  refine Equiv.ext fun i => ?_
  have hi := congrFun (congrFun h i) (σ⁻¹ i)
  simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Matrix.one_apply] at hi
  by_cases h' : i = σ.symm i
  · simpa using congrArg σ h'
  · rw [if_neg h'] at hi
    exact absurd hi hs

/-- The cyclic element is the lift of the three-cycle `finRotate 3`, which is even and so
  needs no sign. -/
lemma su3Perm_eq_su3Weyl : su3Perm = su3Weyl (finRotate 3) := by
  apply Subtype.ext
  rw [su3Weyl_coe, su3Perm_coe]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.permMatrixHom_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply] <;>
    decide

/-- The `SU(3)` transposition Weyl element, the lift of the transposition `(0 1)`. It is
  minus the permutation matrix of the transposition: negating a `3 × 3` matrix flips the
  sign of its determinant, which is exactly the correction an odd permutation needs. Being
  minus an involution it is again an involution, unlike the `SU(2)` Weyl element, which
  squares to `-1`. -/
noncomputable def su3Transp : specialUnitaryGroup (Fin 3) ℂ := su3Weyl (Equiv.swap 0 1)

/-- The underlying matrix of the transposition element. -/
lemma su3Transp_coe :
    (su3Transp : specialUnitaryGroup (Fin 3) ℂ).1 = !![0, -1, 0; -1, 0, 0; 0, 0, -1] := by
  rw [su3Transp, su3Weyl_coe]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.permMatrixHom_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply,
      Equiv.swap_apply_def]

/-- The transposition element squares to the identity, so it has order two in `SU(3)`. -/
lemma su3Transp_mul_self : su3Transp * su3Transp = 1 := by
  rw [su3Transp, ← map_mul,
    show (Equiv.swap (0 : Fin 3) 1) * Equiv.swap (0 : Fin 3) 1 = 1 from by decide, map_one]

/-- The defining relation of `S₃`: conjugating the three-cycle by the transposition inverts
  it. This is what stops the two elements from being graded by a single abelian group. -/
lemma su3Transp_mul_su3Perm_mul_su3Transp :
    su3Transp * su3Perm * su3Transp = su3Perm⁻¹ := by
  rw [su3Transp, su3Perm_eq_su3Weyl, ← map_mul, ← map_mul, ← map_inv]
  congr 1
  decide

/-- The Weyl group as gauge transformations: trivial on isospin and hypercharge. -/
noncomputable def gaugeSU3Weyl : Equiv.Perm (Fin 3) →* GaugeGroupI where
  toFun σ := (su3Weyl σ, 1, 1)
  map_one' := by simp [Prod.ext_iff]
  map_mul' σ τ := by simp [map_mul]

/-- The cyclic gauge element is the lift of the three-cycle. -/
lemma gaugeSU3Perm_eq_gaugeSU3Weyl : gaugeSU3Perm = gaugeSU3Weyl (finRotate 3) := by
  rw [gaugeSU3Perm, gaugeSU3Weyl]
  simp [su3Perm_eq_su3Weyl]

/-- The transposition as a gauge transformation: trivial on isospin and hypercharge. -/
noncomputable def gaugeSU3Transp : GaugeGroupI := ⟨su3Transp, 1, 1⟩

/-- The transposition gauge element is the lift of the transposition `(0 1)`. -/
lemma gaugeSU3Transp_eq_gaugeSU3Weyl : gaugeSU3Transp = gaugeSU3Weyl (Equiv.swap 0 1) := rfl

/-- The cyclic gauge element has order three. -/
lemma gaugeSU3Perm_pow_three : gaugeSU3Perm ^ 3 = 1 := by
  rw [gaugeSU3Perm_eq_gaugeSU3Weyl, ← map_pow,
    show (finRotate 3) ^ 3 = 1 from by decide, map_one]

/-- The transposition gauge element is an involution. -/
lemma gaugeSU3Transp_mul_self : gaugeSU3Transp * gaugeSU3Transp = 1 := by
  rw [gaugeSU3Transp_eq_gaugeSU3Weyl, ← map_mul,
    show (Equiv.swap (0 : Fin 3) 1) * Equiv.swap (0 : Fin 3) 1 = 1 from by decide, map_one]

/-- The `S₃` relation between the two gauge elements, in the form used below: moving the
  three-cycle past the transposition replaces it by its square. -/
lemma gaugeSU3Perm_mul_gaugeSU3Transp :
    gaugeSU3Perm * gaugeSU3Transp = gaugeSU3Transp * gaugeSU3Perm * gaugeSU3Perm := by
  rw [gaugeSU3Perm_eq_gaugeSU3Weyl, gaugeSU3Transp_eq_gaugeSU3Weyl, ← map_mul, ← map_mul,
    ← map_mul]
  congr 1
  decide

/-!

## C. The cube-root character of `ZMod 3`

-/

/-- The primitive cube root of unity `ω = exp (2 π i / 3)`. -/
noncomputable def su3Omega : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I / 3)

/-- `ω` is a primitive cube root of unity. -/
lemma su3Omega_isPrimitiveRoot : IsPrimitiveRoot su3Omega 3 := by
  have h := Complex.isPrimitiveRoot_exp 3 (by norm_num)
  simpa [su3Omega] using h

/-- `ω` cubes to one. -/
@[simp] lemma su3Omega_pow_three : su3Omega ^ 3 = 1 :=
  su3Omega_isPrimitiveRoot.pow_eq_one

/-- `ω` is nonzero, being a value of the complex exponential. -/
lemma su3Omega_ne_zero : su3Omega ≠ 0 := Complex.exp_ne_zero _

/-- Powers of `ω` only see the exponent modulo three. -/
lemma su3Omega_pow_mod (m : ℕ) : su3Omega ^ (m % 3) = su3Omega ^ m := by
  conv_rhs => rw [← Nat.div_add_mod m 3]
  rw [pow_add, pow_mul, su3Omega_pow_three, one_pow, one_mul]

/-- The cube root of unity `ω ^ k` attached to a grade `k : ZMod 3`: the eigenvalue of the
  cyclic element on the `k` piece of a decomposition. -/
noncomputable def su3PermSign (k : ZMod 3) : ℂ := su3Omega ^ k.val

/-- The grade-zero sign is `1`. -/
@[simp] lemma su3PermSign_zero : su3PermSign 0 = 1 := by
  rw [su3PermSign, show (0 : ZMod 3).val = 0 from by decide, pow_zero]

/-- The grade-one sign is `ω`. -/
@[simp] lemma su3PermSign_one : su3PermSign 1 = su3Omega := by
  rw [su3PermSign, show (1 : ZMod 3).val = 1 from by decide, pow_one]

/-- The grade-two sign is `ω ^ 2`. -/
@[simp] lemma su3PermSign_two : su3PermSign 2 = su3Omega ^ 2 := by
  rw [su3PermSign, show (2 : ZMod 3).val = 2 from by decide]

/-- The sign is a character: grades add under multiplication because the cube roots of
  unity multiply. -/
lemma su3PermSign_add (k l : ZMod 3) :
    su3PermSign (k + l) = su3PermSign k * su3PermSign l := by
  rw [su3PermSign, su3PermSign, su3PermSign, ZMod.val_add, su3Omega_pow_mod, pow_add]

/-- Every sign is nonzero, being a root of unity. -/
lemma su3PermSign_ne_zero (k : ZMod 3) : su3PermSign k ≠ 0 :=
  pow_ne_zero _ su3Omega_ne_zero

/-- The three cube roots of unity are distinct, so the pieces of a decomposition sit in
  eigenspaces at distinct eigenvalues and are automatically independent. -/
lemma su3PermSign_injective : Function.Injective su3PermSign := by
  intro k l hkl
  simp only [su3PermSign] at hkl
  exact ZMod.val_injective 3
    (su3Omega_isPrimitiveRoot.pow_inj (ZMod.val_lt k) (ZMod.val_lt l) hkl)

/-- Negating a grade squares its sign, because `-k = k + k` in `ZMod 3`. The Weyl group acts
  on the grades by negation, so this is the sign seen after applying the transposition. -/
lemma su3PermSign_neg (k : ZMod 3) : su3PermSign (-k) = su3PermSign k * su3PermSign k := by
  have h : ∀ j : ZMod 3, -j = j + j := by decide
  rw [h, su3PermSign_add]

/-- The three powers of the sign at a nonzero grade sum to zero. This is the orthogonality of
  the character `k ↦ ω ^ k` against the trivial one, and it is why the symmetrizer of the
  cyclic subgroup kills everything of nonzero grade. -/
lemma su3PermSign_symmetrizer {k : ZMod 3} (hk : k ≠ 0) :
    1 + su3PermSign k + su3PermSign k ^ 2 = 0 := by
  have hω : 1 + su3Omega + su3Omega ^ 2 = 0 := by
    have h := su3Omega_isPrimitiveRoot.geom_sum_eq_zero (by norm_num)
    simpa [Finset.sum_range_succ] using h
  have hcases : ∀ j : ZMod 3, j = 0 ∨ j = 1 ∨ j = 2 := by decide
  rcases hcases k with rfl | rfl | rfl
  · exact absurd rfl hk
  · rw [su3PermSign_one]
    exact hω
  · rw [su3PermSign_two]
    linear_combination hω + su3Omega * su3Omega_pow_three

end StandardModel
