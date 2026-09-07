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
# `SU(3)` permutation decompositions

## i. Overview

An `SU(3)` permutation decomposition of a submodule `V` is a `ZMod 3`-indexed family of
subspaces whose supremum is `V`, the grade-`k` piece scaled by `ω ^ k` under the `SU(3)`
element

  `su3Perm = !![0, 0, 1; 1, 0, 0; 0, 1, 0]`,

the cyclic colour rotation. On a colour triplet it sends `(a, b, c)` to `(c, a, b)`,
cycling the three colours and so cycling the three colour weights that the first two
coordinates of a `GaugeWeight` record.

`su3Perm` is the lift to `SU(3)` of a three-cycle in the Weyl group `S₃`. A three-cycle is
an even permutation, so its permutation matrix already has determinant `1`: unlike the
`SU(2)` transposition, which has to be twisted by a sign to land in `SU(2)`, the cyclic
matrix needs no phase correction at all.

`su3Perm` cubes to `1`, so it has order three in `SU(3)` and `rep gaugeSU3Perm` satisfies
`T ^ 3 = 1`. Its spectrum is therefore contained in the cube roots of unity, and the index
group is `ZMod 3` with eigenvalue `ω ^ k` for `ω = exp (2 π i / 3)` — multiplicative in
`k`, which is what makes the grading add under multiplication, exactly as gauge weights do
in `GaugeWeightDecomposition`. Because `ZMod 3` is finite there is no support field: the
finiteness that `GaugeWeightDecomposition.supp` has to record is automatic here.

The three grades separate the colour directions. A colour triplet splits into the three
lines spanned by `e_r + ω ^ (-k) • e_g + ω ^ (-2 * k) • e_b`, one in each grade, and a
colour contraction, being cyclically symmetric, lands in grade `0`. The grading group has
to be `ZMod 3` rather than the `ZMod 4` of the `SU(2)` file precisely because the element
used here has order three: on `ZMod 4` the character `k ↦ ω ^ k` would not be well defined.

The three-cycle generates only the alternating subgroup `A₃` of the Weyl group `S₃` of
`SU(3)`. The whole of `S₃` is available here too: `su3Weyl` sends a permutation `σ` to its
permutation matrix scaled by the sign of `σ`, which lands in `SU(3)` because the dimension
is odd, and is a group homomorphism because both factors are multiplicative. It is
injective, so `S₃` sits inside `SU(3)` as a genuine subgroup — a point on which `SU(3)`
differs from `SU(2)`, whose Weyl group lifts only to an element of order four.
`su3Transp = !![0, -1, 0; -1, 0, 0; 0, 0, -1]` is the lift of the transposition `(0 1)`; it
squares to `1`, and `t c t = c⁻¹` for `c` the three-cycle.

That last relation is why the file cannot simply carry on grading. A grading by a group is
a decomposition into simultaneous eigenspaces, so it sees only characters of an abelian
group; `S₃` is not abelian, and of its three irreducible representations — the trivial one,
the sign one, and a two-dimensional standard one — the last is not one dimensional and has
no character to grade by. Concretely `t c t = c⁻¹` says that conjugating by the
transposition inverts the three-cycle, so `rep gaugeSU3Transp` carries the grade-`k` piece
to the grade-`(-k)` piece: it does not preserve the grading, it permutes it, exchanging
grades `1` and `2` and fixing only grade `0`. This is `SU3PermDecomposition.mapTransp`.

What replaces the grading is the isotypic decomposition. Writing `T` for the three-cycle
and `R` for the transposition, the three isotypic subspaces of `B` are

  `triv = {x | T x = x and R x = x}`,  `sign = {x | T x = x and R x = -x}`,
  `std = {x | x + T x + T ^ 2 x = 0}`,

and `su3WeylIsotypic_iSup` proves they span `B` while `su3WeylIsotypic_iSupIndep` proves
they are independent, so `B` is their internal direct sum. The last of the three is the
kernel of the symmetrizer `1 + T + T ^ 2` of the cyclic subgroup, three times the projection
onto the vectors that the three-cycle fixes; over `ℂ` every representation of a finite group
is semisimple, and these statements are that semisimplicity made explicit for `S₃`.
`SU3WeylDecomposition` is the sieve version, a family of subspaces of pure isotype with
supremum `V`, and `SU3WeylDecomposition.ofStable` builds one for every `V` stable under the
two elements.

Comparing with the grading: grade `0` is the part the three-cycle fixes and splits into
`triv` and `sign` by the sign of the transposition, while grades `1` and `2`, which the
transposition exchanges, together make up the standard piece. That pairing of a `ZMod 3`
orbit into a two-dimensional irreducible is Clifford theory for `A₃ ⊴ S₃` written out by
hand, and it is `SU3PermDecomposition.toWeyl` in the other direction. An isotypic
decomposition is not a grading and does not pretend to be one: there is no analogue of
`SU3PermDecomposition.mul`, because the tensor square of the standard representation
contains all three irreducibles at once. What does survive is the quotient `S₃ ⧸ A₃`, under
which `triv` and `sign` multiply by the rule of signs; see `su3WeylIsotypic_mul_triv_triv`
and its two companions.

## ii. A warning: grade zero is weaker than invariance

Like the colour weight, this is a *sieve* rather than a characterization.
`mem_zero_of_invariant` says an invariant element has grade zero, and there is no converse.
What it buys is a genuine sharpening of the colour weight in `GaugeWeightDecomposition`,
whose weight-zero piece cannot separate the colour singlet from the neutral components of a
higher multiplet — the Cartan-neutral part of the adjoint is three dimensional, not one.
Because `su3Perm` cycles the three colours it acts on the colour-weight-zero subspace, and
its grade-`1` and grade-`2` parts are thrown away by this sieve.

The sieve cannot be pushed further by grading alone. A grading sees only the cyclic group
generated by the element it uses, and the invariants of a `ZMod 3` subgroup of `SU(3)` are
far larger than the `SU(3)` invariants. Even combining this grading with the full colour
weight only reaches the normalizer of the maximal torus; cutting the remainder down needs
the continuous symmetry, not another grading.

Passing to the whole Weyl group sharpens the sieve, but by a finite amount, and it does not
close that gap. `SU3WeylDecomposition.mem_triv_of_invariant` says an invariant element is
of trivial isotype, which is strictly stronger than having grade zero: the sign isotype is
discarded too, and it is genuinely occupied — the three-cycle fixes a two-dimensional space
of root vectors in the adjoint, and the transposition splits it one dimension into `triv`
and one into `sign`. But `S₃` is a finite group, and the invariants of a finite subgroup
remain far larger than the `SU(3)` invariants; the `SU(3)`-invariance of the colour
contraction of three triplets, for instance, is not decided by any of this. Grading by the
torus and sieving by the Weyl group together decide exactly what happens on the normalizer
of the maximal torus, and no more. The argument that closes the remaining gap has to be a
continuous one.

## iii. Key results

- `su3Perm` : the `SU(3)` cyclic Weyl element `!![0, 0, 1; 1, 0, 0; 0, 1, 0]`, and
  `gaugeSU3Perm` its image in the gauge group.
- `su3Weyl` : the Weyl group `S₃` as a subgroup of `SU(3)`, with `su3Transp` the lift of a
  transposition and `gaugeSU3Weyl` the version landing in the gauge group.
- `su3Omega` : the primitive cube root of unity `exp (2 π i / 3)`.
- `su3PermSign` : the character `k ↦ ω ^ k` on `ZMod 3`, injective and multiplicative.
- `SU3PermDecomposition` : a `ZMod 3`-graded family of pure-sign subspaces with supremum `V`.
- `SU3PermDecomposition.sup` : two decompositions combine gradewise into one of `V ⊔ V'`.
- `SU3PermDecomposition.mul` : grades add under multiplication, decomposing `V * V'`.
- `SU3PermDecomposition.mem_zero_of_invariant` : a gauge-invariant element has grade zero.
- `SU3PermDecomposition.mapTransp` : the transposition carries a decomposition to one of the
  image submodule, with the grades inverted.
- `su3WeylIsotypic` : the three isotypic subspaces of `S₃`, spanning `B` by
  `su3WeylIsotypic_iSup` and independent by `su3WeylIsotypic_iSupIndep`.
- `SU3WeylDecomposition` : a family of subspaces of pure isotype with supremum `V`, built for
  every `S₃`-stable `V` by `SU3WeylDecomposition.ofStable`.
- `SU3WeylDecomposition.mem_triv_of_invariant` : a gauge-invariant element is of trivial
  isotype, strictly finer than having grade zero.

## iv. Table of contents

- A. The `SU(3)` cyclic Weyl element
- B. The Weyl group `S₃` inside `SU(3)`
- C. The cube-root character of `ZMod 3`
- D. `SU(3)` permutation decompositions
- E. Joins
- F. Products
- G. Invariants
- H. The transposition on the cyclic grades
- I. The isotypic subspaces of `S₃`
- J. `S₃` isotypic decompositions

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

/-!

## D. `SU(3)` permutation decompositions

-/

variable {B : Type*} [Ring B] [Algebra ℂ B]

/-- An `SU(3)` permutation decomposition of a submodule `V`: a `ZMod 3`-graded family of
  subspaces of pure sign under the cyclic element `gaugeSU3Perm`, whose supremum is `V`.

  Unlike `GaugeWeightDecomposition` there is no support field — `ZMod 3` is finite, so the
  finiteness condition is automatic. The three grades carry the three cube roots of
  unity. -/
structure SU3PermDecomposition (rep : Representation ℂ GaugeGroupI B)
    (V : Submodule ℂ B) where
  /-- The grade `k` piece of the decomposition. -/
  piece : ZMod 3 → Submodule ℂ B
  /-- Each piece is of pure sign under the cyclic element. -/
  piece_le : ∀ k, ∀ x, x ∈ piece k → rep gaugeSU3Perm x = su3PermSign k • x
  /-- The pieces exhaust `V`. -/
  iSup_piece : (⨆ k, piece k) = V

namespace SU3PermDecomposition

variable {rep : Representation ℂ GaugeGroupI B} {V V' : Submodule ℂ B}

/-- The grade-`k` piece lies in the `su3PermSign k` eigenspace of the cyclic element. This
  is `piece_le` phrased as an inequality of submodules. -/
lemma piece_le_eigenspace (d : SU3PermDecomposition rep V) (k : ZMod 3) :
    d.piece k ≤ Module.End.eigenspace (rep gaugeSU3Perm) (su3PermSign k) :=
  fun _ hy => Module.End.mem_eigenspace_iff.mpr (d.piece_le k _ hy)

/-- Transport a decomposition along an equality of submodules. -/
def copy (d : SU3PermDecomposition rep V) (W : Submodule ℂ B) (hW : W = V) :
    SU3PermDecomposition rep W where
  piece := d.piece
  piece_le := d.piece_le
  iSup_piece := by rw [d.iSup_piece, hW]

/-- Copying leaves the pieces unchanged. -/
@[simp]
lemma copy_piece (d : SU3PermDecomposition rep V) (W : Submodule ℂ B) (hW : W = V) :
    (d.copy W hW).piece = d.piece := rfl

/-- The zero submodule carries the trivial decomposition, with every grade empty. This is
  the unit for `sup`, and the decomposition of every submodule that turns out to vanish. -/
def bot : SU3PermDecomposition rep (⊥ : Submodule ℂ B) where
  piece _ := ⊥
  piece_le k x hx := by
    rw [Submodule.mem_bot] at hx
    subst hx
    simp
  iSup_piece := by simp

/-- Every piece of the trivial decomposition is the zero submodule. -/
@[simp]
lemma bot_piece (k : ZMod 3) : (bot (rep := rep)).piece k = ⊥ := rfl

/-!

## E. Joins

-/

/-- The join of two decompositions: the pieces and suprema combine gradewise, decomposing
  `V ⊔ V'`. -/
noncomputable def sup (d : SU3PermDecomposition rep V) (d' : SU3PermDecomposition rep V') :
    SU3PermDecomposition rep (V ⊔ V') where
  piece k := d.piece k ⊔ d'.piece k
  piece_le k x hx :=
    Module.End.mem_eigenspace_iff.mp
      (sup_le (d.piece_le_eigenspace k) (d'.piece_le_eigenspace k) hx)
  iSup_piece := by
    rw [iSup_sup_eq, d.iSup_piece, d'.iSup_piece]

/-- The pieces of a join are the joins of the pieces. -/
@[simp]
lemma sup_piece (d : SU3PermDecomposition rep V) (d' : SU3PermDecomposition rep V')
    (k : ZMod 3) : (d.sup d').piece k = d.piece k ⊔ d'.piece k := rfl

/-!

## F. Products

-/

/-- The product of two decompositions: grades add under multiplication, so the grade-`k`
  piece of `V * V'` is spanned by the products of pieces whose grades sum to `k`.

  Multiplicativity of the representation is a hypothesis rather than a field: a
  `Representation` records only a linear action. -/
noncomputable def mul (hmul : ∀ (g : GaugeGroupI) (x y : B), rep g (x * y) = rep g x * rep g y)
    (d : SU3PermDecomposition rep V) (d' : SU3PermDecomposition rep V') :
    SU3PermDecomposition rep (V * V') where
  piece k := ⨆ k₁, ⨆ k₂, ⨆ _ : k₁ + k₂ = k, d.piece k₁ * d'.piece k₂
  piece_le k x hx := by
    have key : (⨆ k₁, ⨆ k₂, ⨆ _ : k₁ + k₂ = k, d.piece k₁ * d'.piece k₂)
        ≤ Module.End.eigenspace (rep gaugeSU3Perm) (su3PermSign k) := by
      refine iSup_le fun k₁ => iSup_le fun k₂ => iSup_le fun hk => ?_
      refine Submodule.mul_le.mpr fun m hm n hn => ?_
      refine Module.End.mem_eigenspace_iff.mpr ?_
      rw [hmul, d.piece_le k₁ m hm, d'.piece_le k₂ n hn, smul_mul_smul_comm,
        ← su3PermSign_add, hk]
    exact Module.End.mem_eigenspace_iff.mp (key hx)
  iSup_piece := by
    refine le_antisymm (iSup_le fun k => iSup_le fun k₁ => iSup_le fun k₂ =>
      iSup_le fun _ => ?_) ?_
    · exact mul_le_mul' ((le_iSup d.piece k₁).trans d.iSup_piece.le)
        ((le_iSup d'.piece k₂).trans d'.iSup_piece.le)
    · have hV : (⨆ k₁, d.piece k₁) * (⨆ k₂, d'.piece k₂) = V * V' := by
        rw [d.iSup_piece, d'.iSup_piece]
      rw [← hV, Submodule.iSup_mul]
      refine iSup_le fun k₁ => ?_
      rw [Submodule.mul_iSup]
      refine iSup_le fun k₂ => ?_
      exact le_iSup_of_le (k₁ + k₂)
        (le_iSup_of_le k₁ (le_iSup_of_le k₂ (le_iSup_of_le rfl le_rfl)))

/-- The grade-`k` piece of a product, as a double join over pairs of grades summing to
  `k`. -/
lemma mul_piece (hmul : ∀ (g : GaugeGroupI) (x y : B), rep g (x * y) = rep g x * rep g y)
    (d : SU3PermDecomposition rep V) (d' : SU3PermDecomposition rep V') (k : ZMod 3) :
    (d.mul hmul d').piece k = ⨆ k₁, ⨆ k₂, ⨆ _ : k₁ + k₂ = k, d.piece k₁ * d'.piece k₂ := rfl

/-- The grade-`k` piece of a product, with the second grade solved for: the double join
  collapses to a single one. -/
lemma mul_piece_eq_sub
    (hmul : ∀ (g : GaugeGroupI) (x y : B), rep g (x * y) = rep g x * rep g y)
    (d : SU3PermDecomposition rep V) (d' : SU3PermDecomposition rep V') (k : ZMod 3) :
    (d.mul hmul d').piece k = ⨆ k₁, d.piece k₁ * d'.piece (k - k₁) := by
  rw [mul_piece]
  refine le_antisymm (iSup_le fun k₁ => iSup_le fun k₂ => iSup_le fun hk => ?_) ?_
  · exact le_iSup_of_le k₁ (by rw [eq_sub_of_add_eq' hk])
  · exact iSup_le fun k₁ =>
      le_iSup_of_le k₁ (le_iSup_of_le (k - k₁) (le_iSup_of_le (add_sub_cancel k₁ k) le_rfl))

/-- The grade-`k` piece of a product, written out. `ZMod 3` has three elements, so the
  join is a three-term one. -/
lemma mul_piece_eq (hmul : ∀ (g : GaugeGroupI) (x y : B), rep g (x * y) = rep g x * rep g y)
    (d : SU3PermDecomposition rep V) (d' : SU3PermDecomposition rep V') (k : ZMod 3) :
    (d.mul hmul d').piece k
      = d.piece 0 * d'.piece k ⊔ d.piece 1 * d'.piece (k - 1)
        ⊔ d.piece 2 * d'.piece (k - 2) := by
  have hcases : ∀ j : ZMod 3, j = 0 ∨ j = 1 ∨ j = 2 := by decide
  rw [mul_piece_eq_sub]
  refine le_antisymm (iSup_le fun k₁ => ?_) (sup_le (sup_le ?_ ?_) ?_)
  · rcases hcases k₁ with rfl | rfl | rfl
    · rw [sub_zero]
      exact le_sup_of_le_left le_sup_left
    · exact le_sup_of_le_left le_sup_right
    · exact le_sup_right
  · exact le_iSup_of_le 0 (by rw [sub_zero])
  · exact le_iSup_of_le 1 le_rfl
  · exact le_iSup_of_le 2 le_rfl

/-- The unit submodule has grade zero: the identity of `B` is fixed by every gauge
  transformation, provided the representation preserves the unit. -/
noncomputable def one (hone : ∀ g : GaugeGroupI, rep g 1 = 1) :
    SU3PermDecomposition rep (1 : Submodule ℂ B) where
  piece k := if k = 0 then 1 else ⊥
  piece_le := by
    intro k x hx
    rcases eq_or_ne k 0 with rfl | hk
    · rw [if_pos rfl, Submodule.one_eq_span, Submodule.mem_span_singleton] at hx
      obtain ⟨c, rfl⟩ := hx
      rw [map_smul, hone, su3PermSign_zero, one_smul]
    · rw [if_neg hk, Submodule.mem_bot] at hx
      subst hx
      simp
  iSup_piece := by
    refine le_antisymm (iSup_le fun k => ?_) (le_iSup_of_le 0 (le_of_eq (if_pos rfl).symm))
    by_cases hk : k = 0
    · rw [if_pos hk]
    · rw [if_neg hk]
      exact bot_le

/-- The unit decomposition is concentrated in grade zero. -/
@[simp]
lemma one_piece (hone : ∀ g : GaugeGroupI, rep g 1 = 1) (k : ZMod 3) :
    (one (B := B) (rep := rep) hone).piece k = if k = 0 then 1 else ⊥ := rfl

/-- Powers of a decomposed submodule: grades add, so `V ^ n` inherits a decomposition, built
  by iterating `mul` from `one`. -/
noncomputable def pow (hone : ∀ g : GaugeGroupI, rep g 1 = 1)
    (hmul : ∀ (g : GaugeGroupI) (x y : B), rep g (x * y) = rep g x * rep g y)
    (d : SU3PermDecomposition rep V) :
    (n : ℕ) → SU3PermDecomposition rep (V ^ n)
  | 0 => (one hone).copy _ (pow_zero V)
  | (n + 1) => ((pow hone hmul d n).mul hmul d).copy _ (pow_succ V n)

/-- The zeroth power decomposition is the unit one. -/
@[simp]
lemma pow_zero_piece (hone : ∀ g : GaugeGroupI, rep g 1 = 1)
    (hmul : ∀ (g : GaugeGroupI) (x y : B), rep g (x * y) = rep g x * rep g y)
    (d : SU3PermDecomposition rep V) (k : ZMod 3) :
    (d.pow hone hmul 0).piece k = if k = 0 then 1 else ⊥ := rfl

/-- The pieces of a successor power, unfolded one step of `mul`. -/
@[simp]
lemma pow_succ_piece (hone : ∀ g : GaugeGroupI, rep g 1 = 1)
    (hmul : ∀ (g : GaugeGroupI) (x y : B), rep g (x * y) = rep g x * rep g y)
    (d : SU3PermDecomposition rep V) (n : ℕ) (k : ZMod 3) :
    (d.pow hone hmul (n + 1)).piece k
      = ⨆ k₁, ⨆ k₂, ⨆ _ : k₁ + k₂ = k, (d.pow hone hmul n).piece k₁ * d.piece k₂ := rfl

/-!

## G. Invariants

-/

/-- A gauge-invariant element has grade zero. Only invariance under the single cyclic
  element `gaugeSU3Perm` is used: the other pieces lie in eigenspaces at `ω` and `ω ^ 2`,
  both distinct from `1`.

  There is no converse; see the warning in the module docstring. -/
lemma mem_zero_of_invariant (d : SU3PermDecomposition rep V) {x : B} (hx : x ∈ V)
    (hV : ∀ g : GaugeGroupI, rep g x = x) : x ∈ d.piece 0 := by
  have hdisj : Disjoint
      (Module.End.eigenspace (rep gaugeSU3Perm) (su3PermSign 0))
      (⨆ k, ⨆ _ : k ≠ (0 : ZMod 3), d.piece k) :=
    (((Module.End.eigenspaces_iSupIndep (rep gaugeSU3Perm : Module.End ℂ B)).comp
      su3PermSign_injective) 0).mono_right (iSup₂_mono fun k _ => d.piece_le_eigenspace k)
  have key : (⨆ k, d.piece k)
      ⊓ Module.End.eigenspace (rep gaugeSU3Perm) (su3PermSign 0) ≤ d.piece 0 := by
    rw [iSup_split_single d.piece 0, sup_inf_assoc_of_le _ (d.piece_le_eigenspace 0)]
    exact sup_le le_rfl (hdisj.symm.le_bot.trans bot_le)
  refine key ⟨?_, Module.End.mem_eigenspace_iff.mpr ?_⟩
  · rw [d.iSup_piece]
    exact hx
  · rw [su3PermSign_zero, one_smul]
    exact hV _

end SU3PermDecomposition

/-!

## H. The transposition on the cyclic grades

-/

/-- The three-cycle acts with order three in any representation of the gauge group. -/
lemma rep_gaugeSU3Perm_cube (rep : Representation ℂ GaugeGroupI B) (x : B) :
    rep gaugeSU3Perm (rep gaugeSU3Perm (rep gaugeSU3Perm x)) = x := by
  have h : (rep gaugeSU3Perm : Module.End ℂ B) ^ 3 = 1 := by
    rw [← map_pow, gaugeSU3Perm_pow_three, map_one]
  have h2 := congrArg (fun f : Module.End ℂ B => f x) h
  simpa [pow_succ, Module.End.mul_apply] using h2

/-- The transposition acts as an involution in any representation of the gauge group. -/
lemma rep_gaugeSU3Transp_transp (rep : Representation ℂ GaugeGroupI B) (x : B) :
    rep gaugeSU3Transp (rep gaugeSU3Transp x) = x := by
  have h : (rep gaugeSU3Transp : Module.End ℂ B) * rep gaugeSU3Transp = 1 := by
    rw [← map_mul, gaugeSU3Transp_mul_self, map_one]
  have h2 := congrArg (fun f : Module.End ℂ B => f x) h
  simpa [Module.End.mul_apply] using h2

/-- The `S₃` relation in a representation: moving the three-cycle past the transposition
  replaces it by its square. -/
lemma rep_gaugeSU3Perm_gaugeSU3Transp (rep : Representation ℂ GaugeGroupI B) (x : B) :
    rep gaugeSU3Perm (rep gaugeSU3Transp x)
      = rep gaugeSU3Transp (rep gaugeSU3Perm (rep gaugeSU3Perm x)) := by
  have h : (rep gaugeSU3Perm : Module.End ℂ B) * rep gaugeSU3Transp
      = rep gaugeSU3Transp * rep gaugeSU3Perm * rep gaugeSU3Perm := by
    rw [← map_mul, ← map_mul, ← map_mul, gaugeSU3Perm_mul_gaugeSU3Transp]
  have h2 := congrArg (fun f : Module.End ℂ B => f x) h
  simpa [Module.End.mul_apply] using h2

/-- The transposition sends a vector of grade `k` to one of grade `-k`. The Weyl group does
  not preserve the cyclic grading: it permutes the grades, fixing only grade `0` and
  exchanging grades `1` and `2`. -/
lemma rep_gaugeSU3Perm_transp {rep : Representation ℂ GaugeGroupI B} {x : B} {k : ZMod 3}
    (hx : rep gaugeSU3Perm x = su3PermSign k • x) :
    rep gaugeSU3Perm (rep gaugeSU3Transp x)
      = su3PermSign (-k) • rep gaugeSU3Transp x := by
  rw [rep_gaugeSU3Perm_gaugeSU3Transp, hx, map_smul, hx, smul_smul, map_smul,
    su3PermSign_neg]

/-- A supremum over `ZMod 3`, written out as a three-term join. -/
lemma iSup_zmod_three (f : ZMod 3 → Submodule ℂ B) : (⨆ k, f k) = f 0 ⊔ f 1 ⊔ f 2 := by
  have hcases : ∀ j : ZMod 3, j = 0 ∨ j = 1 ∨ j = 2 := by decide
  refine le_antisymm (iSup_le fun k => ?_) (sup_le (sup_le ?_ ?_) ?_)
  · rcases hcases k with rfl | rfl | rfl
    · exact le_sup_of_le_left le_sup_left
    · exact le_sup_of_le_left le_sup_right
    · exact le_sup_right
  · exact le_iSup f 0
  · exact le_iSup f 1
  · exact le_iSup f 2

/-- A submodule stable under the transposition is the join of its two eigenparts: the
  transposition is an involution and `2` is invertible, so `x` is the sum of `(x + R x) / 2`
  and `(x - R x) / 2`. -/
lemma sup_inf_eigenspace_gaugeSU3Transp (rep : Representation ℂ GaugeGroupI B)
    (W : Submodule ℂ B) (hstab : ∀ x ∈ W, rep gaugeSU3Transp x ∈ W) :
    W ⊓ Module.End.eigenspace (rep gaugeSU3Transp) 1
      ⊔ W ⊓ Module.End.eigenspace (rep gaugeSU3Transp) (-1) = W := by
  refine le_antisymm (sup_le inf_le_left inf_le_left) fun x hx => ?_
  refine Submodule.mem_sup.mpr ⟨(2 : ℂ)⁻¹ • (x + rep gaugeSU3Transp x),
    ⟨W.smul_mem _ (W.add_mem hx (hstab x hx)), Module.End.mem_eigenspace_iff.mpr ?_⟩,
    (2 : ℂ)⁻¹ • (x - rep gaugeSU3Transp x),
    ⟨W.smul_mem _ (W.sub_mem hx (hstab x hx)), Module.End.mem_eigenspace_iff.mpr ?_⟩, by
      module⟩
  · rw [map_smul, map_add, rep_gaugeSU3Transp_transp]
    module
  · rw [map_smul, map_sub, rep_gaugeSU3Transp_transp]
    module

namespace SU3PermDecomposition

variable {rep : Representation ℂ GaugeGroupI B} {V : Submodule ℂ B}

/-- The transposition carries a decomposition of `V` to a decomposition of the image of `V`,
  with the grades inverted. There is no way to make this a decomposition of `V` itself: the
  Weyl group acts on the cyclic gradings, it does not preserve one. -/
noncomputable def mapTransp (d : SU3PermDecomposition rep V) :
    SU3PermDecomposition rep (V.map (rep gaugeSU3Transp)) where
  piece k := (d.piece (-k)).map (rep gaugeSU3Transp)
  piece_le k x hx := by
    rw [Submodule.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    have h := rep_gaugeSU3Perm_transp (d.piece_le (-k) y hy)
    rwa [neg_neg] at h
  iSup_piece := by
    have h : (⨆ k : ZMod 3, d.piece (-k)) = V :=
      ((Equiv.neg (ZMod 3)).iSup_comp (g := d.piece)).trans d.iSup_piece
    rw [← Submodule.map_iSup, h]

/-- The pieces of the transported decomposition. -/
@[simp]
lemma mapTransp_piece (d : SU3PermDecomposition rep V) (k : ZMod 3) :
    d.mapTransp.piece k = (d.piece (-k)).map (rep gaugeSU3Transp) := rfl

end SU3PermDecomposition

/-!

## I. The isotypic subspaces of `S₃`

-/

/-- The irreducible representations of the Weyl group `S₃`, up to isomorphism. There are
  three of them, of dimensions `1`, `1` and `2`. -/
inductive SU3WeylIrrep
  /-- The trivial representation, on which every permutation acts as the identity. -/
  | triv : SU3WeylIrrep
  /-- The sign representation, on which a permutation acts by its sign. -/
  | sign : SU3WeylIrrep
  /-- The two-dimensional standard representation. -/
  | std : SU3WeylIrrep
deriving DecidableEq

/-- The dimension of each irreducible representation of `S₃`. The squares sum to the order
  of the group: `1 + 1 + 4 = 6`. -/
def SU3WeylIrrep.dim : SU3WeylIrrep → ℕ
  | .triv => 1
  | .sign => 1
  | .std => 2

/-- A supremum over the three irreducibles of `S₃`, written out as a three-term join. -/
lemma iSup_su3WeylIrrep (f : SU3WeylIrrep → Submodule ℂ B) :
    (⨆ r, f r) = f .triv ⊔ f .sign ⊔ f .std := by
  refine le_antisymm (iSup_le fun r => ?_) (sup_le (sup_le ?_ ?_) ?_)
  · cases r
    · exact le_sup_of_le_left le_sup_left
    · exact le_sup_of_le_left le_sup_right
    · exact le_sup_right
  · exact le_iSup f .triv
  · exact le_iSup f .sign
  · exact le_iSup f .std

/-- The symmetrizer of the cyclic subgroup `A₃`, namely `1 + T + T ^ 2` for `T` the
  three-cycle. It is three times the projection onto the vectors that the three-cycle fixes,
  so its kernel is where the three-cycle has no invariant vector at all. -/
noncomputable def su3Symmetrizer (rep : Representation ℂ GaugeGroupI B) : Module.End ℂ B :=
  1 + rep gaugeSU3Perm + rep gaugeSU3Perm ^ 2

/-- The symmetrizer applied to an element. -/
lemma su3Symmetrizer_apply (rep : Representation ℂ GaugeGroupI B) (x : B) :
    su3Symmetrizer rep x
      = x + rep gaugeSU3Perm x + rep gaugeSU3Perm (rep gaugeSU3Perm x) := by
  simp [su3Symmetrizer, sq, Module.End.mul_apply]

/-- The symmetrizer multiplies a vector fixed by the three-cycle by three. -/
lemma su3Symmetrizer_apply_of_perm_eq {rep : Representation ℂ GaugeGroupI B} {x : B}
    (hx : rep gaugeSU3Perm x = x) : su3Symmetrizer rep x = (3 : ℂ) • x := by
  rw [su3Symmetrizer_apply, hx, hx]
  module

/-- The isotypic subspace of `B` for each irreducible representation of `S₃`. The three-cycle
  acts as the identity on the trivial and sign parts, and the transposition by `1` and `-1`
  respectively; the standard part is the kernel of the symmetrizer of the cyclic subgroup.

  These are the honest isotypic components of `B` viewed as a representation of `S₃`: over
  `ℂ` every representation of a finite group is semisimple, and `su3WeylIsotypic_iSup` proves
  that these three subspaces span. -/
noncomputable def su3WeylIsotypic (rep : Representation ℂ GaugeGroupI B) :
    SU3WeylIrrep → Submodule ℂ B
  | .triv => Module.End.eigenspace (rep gaugeSU3Perm) 1
      ⊓ Module.End.eigenspace (rep gaugeSU3Transp) 1
  | .sign => Module.End.eigenspace (rep gaugeSU3Perm) 1
      ⊓ Module.End.eigenspace (rep gaugeSU3Transp) (-1)
  | .std => LinearMap.ker (su3Symmetrizer rep)

/-- Membership of the trivial isotypic subspace: both Weyl elements act as the identity. -/
lemma mem_su3WeylIsotypic_triv_iff {rep : Representation ℂ GaugeGroupI B} {x : B} :
    x ∈ su3WeylIsotypic rep .triv
      ↔ rep gaugeSU3Perm x = x ∧ rep gaugeSU3Transp x = x := by
  simp [su3WeylIsotypic]

/-- Membership of the sign isotypic subspace: the three-cycle acts as the identity and the
  transposition by `-1`. -/
lemma mem_su3WeylIsotypic_sign_iff {rep : Representation ℂ GaugeGroupI B} {x : B} :
    x ∈ su3WeylIsotypic rep .sign
      ↔ rep gaugeSU3Perm x = x ∧ rep gaugeSU3Transp x = -x := by
  simp [su3WeylIsotypic]

/-- Membership of the standard isotypic subspace: the symmetrizer of the cyclic subgroup
  kills the vector. -/
lemma mem_su3WeylIsotypic_std_iff {rep : Representation ℂ GaugeGroupI B} {x : B} :
    x ∈ su3WeylIsotypic rep .std
      ↔ x + rep gaugeSU3Perm x + rep gaugeSU3Perm (rep gaugeSU3Perm x) = 0 := by
  rw [su3WeylIsotypic, LinearMap.mem_ker, su3Symmetrizer_apply]

/-- A vector of nonzero grade is of standard isotype: the symmetrizer kills it because the
  three values of the character at a nonzero grade sum to zero. This is the half of Clifford
  theory that turns the pair of grades `{1, 2}` into the two-dimensional irreducible. -/
lemma mem_su3WeylIsotypic_std_of_grade {rep : Representation ℂ GaugeGroupI B} {x : B}
    {k : ZMod 3} (hk : k ≠ 0)
    (hx : rep gaugeSU3Perm x = su3PermSign k • x) :
    x ∈ su3WeylIsotypic rep .std := by
  rw [mem_su3WeylIsotypic_std_iff, hx, map_smul, hx, smul_smul]
  have hsum : x + su3PermSign k • x + (su3PermSign k * su3PermSign k) • x
      = (1 + su3PermSign k + su3PermSign k ^ 2) • x := by module
  rw [hsum, su3PermSign_symmetrizer hk, zero_smul]

/-- The trivial and sign isotypic subspaces meet only in zero: the transposition cannot act
  both as `1` and as `-1` on a nonzero vector. -/
lemma su3WeylIsotypic_disjoint_triv_sign (rep : Representation ℂ GaugeGroupI B) :
    Disjoint (su3WeylIsotypic rep .triv) (su3WeylIsotypic rep .sign) := by
  rw [disjoint_iff_inf_le]
  intro x hx
  have h1 := (mem_su3WeylIsotypic_triv_iff.mp hx.1).2
  have h2 := (mem_su3WeylIsotypic_sign_iff.mp hx.2).2
  have hxx : (2 : ℂ) • x = 0 := by
    rw [two_smul]
    exact neg_eq_iff_add_eq_zero.mp (h2.symm.trans h1)
  rcases smul_eq_zero.mp hxx with h | h
  · norm_num at h
  · simpa using h

/-- The standard isotypic subspace meets the vectors fixed by the three-cycle only in zero:
  the symmetrizer multiplies such a vector by three and kills it at the same time. -/
lemma su3WeylIsotypic_disjoint_std (rep : Representation ℂ GaugeGroupI B) :
    Disjoint (Module.End.eigenspace (rep gaugeSU3Perm) 1) (su3WeylIsotypic rep .std) := by
  rw [disjoint_iff_inf_le]
  intro x hx
  have h1 : rep gaugeSU3Perm x = x := by
    simpa using Module.End.mem_eigenspace_iff.mp hx.1
  have h2 : su3Symmetrizer rep x = 0 := LinearMap.mem_ker.mp hx.2
  rw [su3Symmetrizer_apply_of_perm_eq h1] at h2
  rcases smul_eq_zero.mp h2 with h | h
  · norm_num at h
  · simpa using h

/-- The standard isotypic subspace is disjoint from the join of the other two, which both
  consist of vectors fixed by the three-cycle. -/
lemma su3WeylIsotypic_disjoint_std_sup (rep : Representation ℂ GaugeGroupI B) :
    Disjoint (su3WeylIsotypic rep .std)
      (su3WeylIsotypic rep .triv ⊔ su3WeylIsotypic rep .sign) :=
  (su3WeylIsotypic_disjoint_std rep).symm.mono_right (sup_le inf_le_left inf_le_left)

/-- The trivial isotypic subspace is disjoint from the join of the other two. The symmetrizer
  kills the standard part of such a vector and multiplies the other two parts by three, so
  the standard part vanishes; the trivial and sign parts are already disjoint. -/
lemma su3WeylIsotypic_disjoint_triv_sup (rep : Representation ℂ GaugeGroupI B) :
    Disjoint (su3WeylIsotypic rep .triv)
      (su3WeylIsotypic rep .sign ⊔ su3WeylIsotypic rep .std) := by
  rw [disjoint_iff_inf_le]
  intro x hx
  obtain ⟨b, hb, s, hs, rfl⟩ := Submodule.mem_sup.mp hx.2
  have h1 : su3Symmetrizer rep (b + s) = (3 : ℂ) • (b + s) :=
    su3Symmetrizer_apply_of_perm_eq (mem_su3WeylIsotypic_triv_iff.mp hx.1).1
  rw [map_add, su3Symmetrizer_apply_of_perm_eq (mem_su3WeylIsotypic_sign_iff.mp hb).1,
    LinearMap.mem_ker.mp hs, add_zero, smul_add] at h1
  have hs0 : s = 0 := by
    have h2 : (3 : ℂ) • s = 0 := by simpa using sub_eq_zero_of_eq h1.symm
    rcases smul_eq_zero.mp h2 with h | h
    · norm_num at h
    · exact h
  subst hs0
  rw [add_zero] at hx ⊢
  exact (su3WeylIsotypic_disjoint_triv_sign rep).le_bot ⟨hx.1, hb⟩

/-- The sign isotypic subspace is disjoint from the join of the other two, by the same
  argument as for the trivial one: the three-cycle acts as the identity on both. -/
lemma su3WeylIsotypic_disjoint_sign_sup (rep : Representation ℂ GaugeGroupI B) :
    Disjoint (su3WeylIsotypic rep .sign)
      (su3WeylIsotypic rep .triv ⊔ su3WeylIsotypic rep .std) := by
  rw [disjoint_iff_inf_le]
  intro x hx
  obtain ⟨a, ha, s, hs, rfl⟩ := Submodule.mem_sup.mp hx.2
  have h1 : su3Symmetrizer rep (a + s) = (3 : ℂ) • (a + s) :=
    su3Symmetrizer_apply_of_perm_eq (mem_su3WeylIsotypic_sign_iff.mp hx.1).1
  rw [map_add, su3Symmetrizer_apply_of_perm_eq (mem_su3WeylIsotypic_triv_iff.mp ha).1,
    LinearMap.mem_ker.mp hs, add_zero, smul_add] at h1
  have hs0 : s = 0 := by
    have h2 : (3 : ℂ) • s = 0 := by simpa using sub_eq_zero_of_eq h1.symm
    rcases smul_eq_zero.mp h2 with h | h
    · norm_num at h
    · exact h
  subst hs0
  rw [add_zero] at hx ⊢
  exact (su3WeylIsotypic_disjoint_triv_sign rep).symm.le_bot ⟨hx.1, ha⟩

/-- The three isotypic subspaces are independent. Together with `su3WeylIsotypic_iSup` this
  says that `B` is the internal direct sum of its three isotypic parts, which is the isotypic
  decomposition of `B` as a representation of the Weyl group `S₃`. -/
lemma su3WeylIsotypic_iSupIndep (rep : Representation ℂ GaugeGroupI B) :
    iSupIndep (su3WeylIsotypic rep) := by
  intro r
  cases r
  · refine (su3WeylIsotypic_disjoint_triv_sup rep).mono_right (iSup₂_le fun j hj => ?_)
    cases j
    · exact absurd rfl hj
    · exact le_sup_left
    · exact le_sup_right
  · refine (su3WeylIsotypic_disjoint_sign_sup rep).mono_right (iSup₂_le fun j hj => ?_)
    cases j
    · exact le_sup_left
    · exact absurd rfl hj
    · exact le_sup_right
  · refine (su3WeylIsotypic_disjoint_std_sup rep).mono_right (iSup₂_le fun j hj => ?_)
    cases j
    · exact le_sup_left
    · exact le_sup_right
    · exact absurd rfl hj

/-- Every element of a submodule stable under both Weyl elements is a sum of three elements
  of that submodule, one of each isotype. Symmetrizing over the three-cycle and then over the
  transposition produces the trivial and sign parts, and what is left over is killed by the
  symmetrizer. Over `ℂ` this is the semisimplicity of representations of a finite group,
  written out for `S₃`. -/
lemma mem_sup_su3WeylIsotypic {rep : Representation ℂ GaugeGroupI B} {V : Submodule ℂ B}
    (hc : ∀ x ∈ V, rep gaugeSU3Perm x ∈ V) (ht : ∀ x ∈ V, rep gaugeSU3Transp x ∈ V)
    {x : B} (hx : x ∈ V) :
    x ∈ V ⊓ su3WeylIsotypic rep .triv ⊔ V ⊓ su3WeylIsotypic rep .sign
      ⊔ V ⊓ su3WeylIsotypic rep .std := by
  have hyV : (3 : ℂ)⁻¹ • (x + rep gaugeSU3Perm x + rep gaugeSU3Perm (rep gaugeSU3Perm x))
      ∈ V := V.smul_mem _ (V.add_mem (V.add_mem hx (hc x hx)) (hc _ (hc x hx)))
  set y := (3 : ℂ)⁻¹ • (x + rep gaugeSU3Perm x + rep gaugeSU3Perm (rep gaugeSU3Perm x))
    with hy
  have hTy : rep gaugeSU3Perm y = y := by
    rw [hy, map_smul, map_add, map_add, rep_gaugeSU3Perm_cube]
    module
  have hTRy : rep gaugeSU3Perm (rep gaugeSU3Transp y) = rep gaugeSU3Transp y := by
    rw [rep_gaugeSU3Perm_gaugeSU3Transp, hTy, hTy]
  have hRyV : rep gaugeSU3Transp y ∈ V := ht y hyV
  refine Submodule.mem_sup.mpr ⟨(2 : ℂ)⁻¹ • (y + rep gaugeSU3Transp y)
      + (2 : ℂ)⁻¹ • (y - rep gaugeSU3Transp y),
    Submodule.mem_sup.mpr ⟨(2 : ℂ)⁻¹ • (y + rep gaugeSU3Transp y),
      ⟨V.smul_mem _ (V.add_mem hyV hRyV), ?_⟩,
      (2 : ℂ)⁻¹ • (y - rep gaugeSU3Transp y),
      ⟨V.smul_mem _ (V.sub_mem hyV hRyV), ?_⟩, rfl⟩, x - y, ⟨V.sub_mem hx hyV, ?_⟩, by
    module⟩
  · refine mem_su3WeylIsotypic_triv_iff.mpr ⟨?_, ?_⟩
    · rw [map_smul, map_add, hTy, hTRy]
    · rw [map_smul, map_add, rep_gaugeSU3Transp_transp]
      module
  · refine mem_su3WeylIsotypic_sign_iff.mpr ⟨?_, ?_⟩
    · rw [map_smul, map_sub, hTy, hTRy]
    · rw [map_smul, map_sub, rep_gaugeSU3Transp_transp]
      module
  · refine mem_su3WeylIsotypic_std_iff.mpr ?_
    simp only [map_sub]
    rw [hTy, hTy, hy]
    module

/-- The three isotypic subspaces span the whole of `B`. This is the isotypic decomposition
  of `B` as a representation of the Weyl group `S₃`. -/
lemma su3WeylIsotypic_iSup (rep : Representation ℂ GaugeGroupI B) :
    (⨆ r, su3WeylIsotypic rep r) = ⊤ := by
  refine le_antisymm le_top fun x _ => ?_
  have h := mem_sup_su3WeylIsotypic (V := (⊤ : Submodule ℂ B)) (rep := rep)
    (fun _ _ => Submodule.mem_top) (fun _ _ => Submodule.mem_top) (Submodule.mem_top (x := x))
  rw [top_inf_eq, top_inf_eq, top_inf_eq] at h
  rw [iSup_su3WeylIrrep]
  exact h

/-- Two vectors of trivial isotype have a product of trivial isotype. -/
lemma su3WeylIsotypic_mul_triv_triv {rep : Representation ℂ GaugeGroupI B}
    (hmul : ∀ (g : GaugeGroupI) (x y : B), rep g (x * y) = rep g x * rep g y) :
    su3WeylIsotypic rep .triv * su3WeylIsotypic rep .triv
      ≤ su3WeylIsotypic rep .triv := by
  refine Submodule.mul_le.mpr fun m hm n hn => ?_
  rw [mem_su3WeylIsotypic_triv_iff] at hm hn ⊢
  exact ⟨by rw [hmul, hm.1, hn.1], by rw [hmul, hm.2, hn.2]⟩

/-- A vector of trivial isotype times one of sign isotype has sign isotype. -/
lemma su3WeylIsotypic_mul_triv_sign {rep : Representation ℂ GaugeGroupI B}
    (hmul : ∀ (g : GaugeGroupI) (x y : B), rep g (x * y) = rep g x * rep g y) :
    su3WeylIsotypic rep .triv * su3WeylIsotypic rep .sign
      ≤ su3WeylIsotypic rep .sign := by
  refine Submodule.mul_le.mpr fun m hm n hn => ?_
  rw [mem_su3WeylIsotypic_triv_iff] at hm
  rw [mem_su3WeylIsotypic_sign_iff] at hn ⊢
  exact ⟨by rw [hmul, hm.1, hn.1], by rw [hmul, hm.2, hn.2, mul_neg]⟩

/-- Two vectors of sign isotype have a product of trivial isotype: the sign character squares
  to the trivial one. -/
lemma su3WeylIsotypic_mul_sign_sign {rep : Representation ℂ GaugeGroupI B}
    (hmul : ∀ (g : GaugeGroupI) (x y : B), rep g (x * y) = rep g x * rep g y) :
    su3WeylIsotypic rep .sign * su3WeylIsotypic rep .sign
      ≤ su3WeylIsotypic rep .triv := by
  refine Submodule.mul_le.mpr fun m hm n hn => ?_
  rw [mem_su3WeylIsotypic_sign_iff] at hm hn
  rw [mem_su3WeylIsotypic_triv_iff]
  exact ⟨by rw [hmul, hm.1, hn.1], by rw [hmul, hm.2, hn.2, neg_mul_neg]⟩

/-!

## J. `S₃` isotypic decompositions

-/

/-- An `S₃` isotypic decomposition of a submodule `V`: a family of subspaces indexed by the
  irreducible representations of the Weyl group `S₃`, each of pure isotype, whose supremum
  is `V`.

  This is what replaces `SU3PermDecomposition` for the whole Weyl group. It is deliberately
  not a grading: `S₃` is not abelian, its standard representation is two dimensional, and
  there is no character to grade by. Like `SU3PermDecomposition` it is a sieve — the pieces
  are only required to lie inside the isotypic subspaces, not to exhaust them — and
  `ofStable` builds the canonical one for any `S₃`-stable `V`. -/
structure SU3WeylDecomposition (rep : Representation ℂ GaugeGroupI B)
    (V : Submodule ℂ B) where
  /-- The piece of isotype `r`. -/
  isotypic : SU3WeylIrrep → Submodule ℂ B
  /-- Each piece is of pure isotype. -/
  isotypic_le : ∀ r, isotypic r ≤ su3WeylIsotypic rep r
  /-- The pieces exhaust `V`. -/
  iSup_isotypic : (⨆ r, isotypic r) = V

namespace SU3WeylDecomposition

variable {rep : Representation ℂ GaugeGroupI B} {V V' : Submodule ℂ B}

/-- The supremum defining a decomposition, written out as a three-term join. -/
lemma iSup_isotypic_eq (d : SU3WeylDecomposition rep V) :
    d.isotypic .triv ⊔ d.isotypic .sign ⊔ d.isotypic .std = V := by
  rw [← iSup_su3WeylIrrep]
  exact d.iSup_isotypic

/-- Transport a decomposition along an equality of submodules. -/
def copy (d : SU3WeylDecomposition rep V) (W : Submodule ℂ B) (hW : W = V) :
    SU3WeylDecomposition rep W where
  isotypic := d.isotypic
  isotypic_le := d.isotypic_le
  iSup_isotypic := by rw [d.iSup_isotypic, hW]

/-- Copying leaves the pieces unchanged. -/
@[simp]
lemma copy_isotypic (d : SU3WeylDecomposition rep V) (W : Submodule ℂ B) (hW : W = V) :
    (d.copy W hW).isotypic = d.isotypic := rfl

/-- The zero submodule carries the trivial decomposition, with every isotype empty. -/
def bot : SU3WeylDecomposition rep (⊥ : Submodule ℂ B) where
  isotypic _ := ⊥
  isotypic_le _ := bot_le
  iSup_isotypic := by simp

/-- Every piece of the trivial decomposition is the zero submodule. -/
@[simp]
lemma bot_isotypic (r : SU3WeylIrrep) : (bot (rep := rep)).isotypic r = ⊥ := rfl

/-- The join of two decompositions: the pieces combine isotype by isotype, decomposing
  `V ⊔ V'`. Unlike products, joins respect the isotypic splitting. -/
noncomputable def sup (d : SU3WeylDecomposition rep V) (d' : SU3WeylDecomposition rep V') :
    SU3WeylDecomposition rep (V ⊔ V') where
  isotypic r := d.isotypic r ⊔ d'.isotypic r
  isotypic_le r := sup_le (d.isotypic_le r) (d'.isotypic_le r)
  iSup_isotypic := by rw [iSup_sup_eq, d.iSup_isotypic, d'.iSup_isotypic]

/-- The pieces of a join are the joins of the pieces. -/
@[simp]
lemma sup_isotypic (d : SU3WeylDecomposition rep V) (d' : SU3WeylDecomposition rep V')
    (r : SU3WeylIrrep) : (d.sup d').isotypic r = d.isotypic r ⊔ d'.isotypic r := rfl

/-- The canonical isotypic decomposition of a submodule stable under both Weyl elements: the
  piece of isotype `r` is the part of `V` lying in the `r` isotypic subspace of `B`. That
  these exhaust `V` is `mem_sup_su3WeylIsotypic`, the semisimplicity of `S₃` over `ℂ`. -/
noncomputable def ofStable (hc : ∀ x ∈ V, rep gaugeSU3Perm x ∈ V)
    (ht : ∀ x ∈ V, rep gaugeSU3Transp x ∈ V) : SU3WeylDecomposition rep V where
  isotypic r := V ⊓ su3WeylIsotypic rep r
  isotypic_le _ := inf_le_right
  iSup_isotypic := by
    rw [iSup_su3WeylIrrep]
    exact le_antisymm (sup_le (sup_le inf_le_left inf_le_left) inf_le_left)
      fun _ hx => mem_sup_su3WeylIsotypic hc ht hx

/-- The pieces of the canonical decomposition of a stable submodule. -/
@[simp]
lemma ofStable_isotypic (hc : ∀ x ∈ V, rep gaugeSU3Perm x ∈ V)
    (ht : ∀ x ∈ V, rep gaugeSU3Transp x ∈ V) (r : SU3WeylIrrep) :
    (ofStable hc ht).isotypic r = V ⊓ su3WeylIsotypic rep r := rfl

/-- The pieces of a decomposition are independent: they lie inside the isotypic subspaces of
  `B`, which are independent. A decomposition is therefore a direct sum decomposition of `V`,
  and not merely a covering of it. -/
lemma iSupIndep_isotypic (d : SU3WeylDecomposition rep V) : iSupIndep d.isotypic :=
  (su3WeylIsotypic_iSupIndep rep).mono d.isotypic_le

/-- A gauge-invariant element is of trivial isotype. This is strictly finer than
  `SU3PermDecomposition.mem_zero_of_invariant`, which only places it in grade zero: grade
  zero is the join of the trivial and sign isotypes, and this discards the sign one as well.

  The proof is the character projection written by hand. The symmetrizer multiplies the
  invariant element and the trivial and sign parts by three and kills the standard part, so
  the standard part vanishes; the transposition then acts as `1` on the element and on the
  trivial part and as `-1` on the sign part, so the sign part vanishes too.

  There is still no converse; see the warning in the module docstring. -/
lemma mem_triv_of_invariant (d : SU3WeylDecomposition rep V) {x : B} (hx : x ∈ V)
    (hV : ∀ g : GaugeGroupI, rep g x = x) : x ∈ d.isotypic .triv := by
  rw [← d.iSup_isotypic, iSup_su3WeylIrrep] at hx
  obtain ⟨w, hw, s, hs, rfl⟩ := Submodule.mem_sup.mp hx
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hw
  have hta := mem_su3WeylIsotypic_triv_iff.mp (d.isotypic_le .triv ha)
  have htb := mem_su3WeylIsotypic_sign_iff.mp (d.isotypic_le .sign hb)
  have hts : su3Symmetrizer rep s = 0 := LinearMap.mem_ker.mp (d.isotypic_le .std hs)
  have hs0 : s = 0 := by
    have hsum : su3Symmetrizer rep (a + b + s)
        = su3Symmetrizer rep a + su3Symmetrizer rep b + su3Symmetrizer rep s := by
      rw [map_add, map_add]
    rw [su3Symmetrizer_apply_of_perm_eq (hV gaugeSU3Perm),
      su3Symmetrizer_apply_of_perm_eq hta.1, su3Symmetrizer_apply_of_perm_eq htb.1, hts] at hsum
    have h3 : (3 : ℂ) • s = 0 := by
      have := hsum
      rw [smul_add, smul_add] at this
      simpa using sub_eq_zero.mpr this
    rcases smul_eq_zero.mp h3 with h | h
    · norm_num at h
    · exact h
  subst hs0
  have hR : rep gaugeSU3Transp (a + b + 0) = a + b + 0 := hV gaugeSU3Transp
  rw [add_zero, map_add, htb.2, hta.2] at hR
  have hb0 : (2 : ℂ) • b = 0 := by
    rw [two_smul]
    exact neg_eq_iff_add_eq_zero.mp (add_left_cancel hR)
  rcases smul_eq_zero.mp hb0 with h | h
  · norm_num at h
  · rw [h, add_zero, add_zero]
    exact ha

end SU3WeylDecomposition

namespace SU3PermDecomposition

variable {rep : Representation ℂ GaugeGroupI B} {V : Submodule ℂ B}

/-- The two nonzero grades are of standard isotype. Together with `piece_le_eigenspace` at
  grade `0`, this places every cyclic decomposition inside the isotypic picture: grade `0`
  is where the trivial and sign isotypes live, and grades `1` and `2`, which the transposition
  exchanges, make up the standard one. -/
lemma piece_le_su3WeylIsotypic_std (d : SU3PermDecomposition rep V) {k : ZMod 3}
    (hk : k ≠ 0) : d.piece k ≤ su3WeylIsotypic rep .std :=
  fun x hx => mem_su3WeylIsotypic_std_of_grade hk (d.piece_le k x hx)

/-- A cyclic decomposition whose grade-zero piece is stable under the transposition upgrades
  to an isotypic decomposition for the whole Weyl group. Grade zero splits into the trivial
  and sign pieces according to the sign of the transposition, and grades `1` and `2` join to
  give the standard piece. Stability of grade zero is needed and is not automatic: the
  transposition inverts grades, so it does preserve the grade-zero eigenspace of `B`, but the
  grade-zero piece of a decomposition need only sit inside that eigenspace. -/
noncomputable def toWeyl (d : SU3PermDecomposition rep V)
    (hstab : ∀ x ∈ d.piece 0, rep gaugeSU3Transp x ∈ d.piece 0) :
    SU3WeylDecomposition rep V where
  isotypic
  | .triv => d.piece 0 ⊓ Module.End.eigenspace (rep gaugeSU3Transp) 1
  | .sign => d.piece 0 ⊓ Module.End.eigenspace (rep gaugeSU3Transp) (-1)
  | .std => d.piece 1 ⊔ d.piece 2
  isotypic_le r := by
    have h0 : d.piece 0 ≤ Module.End.eigenspace (rep gaugeSU3Perm) 1 := by
      simpa using d.piece_le_eigenspace 0
    cases r
    · exact inf_le_inf_right _ h0
    · exact inf_le_inf_right _ h0
    · exact sup_le (d.piece_le_su3WeylIsotypic_std (by decide))
        (d.piece_le_su3WeylIsotypic_std (by decide))
  iSup_isotypic := by
    rw [iSup_su3WeylIrrep]
    show d.piece 0 ⊓ Module.End.eigenspace (rep gaugeSU3Transp) 1
        ⊔ d.piece 0 ⊓ Module.End.eigenspace (rep gaugeSU3Transp) (-1)
        ⊔ (d.piece 1 ⊔ d.piece 2) = V
    rw [sup_inf_eigenspace_gaugeSU3Transp rep _ hstab, ← sup_assoc, ← iSup_zmod_three]
    exact d.iSup_piece

/-- The trivial piece of the upgraded decomposition. -/
@[simp]
lemma toWeyl_isotypic_triv (d : SU3PermDecomposition rep V)
    (hstab : ∀ x ∈ d.piece 0, rep gaugeSU3Transp x ∈ d.piece 0) :
    (d.toWeyl hstab).isotypic .triv
      = d.piece 0 ⊓ Module.End.eigenspace (rep gaugeSU3Transp) 1 := rfl

/-- The sign piece of the upgraded decomposition. -/
@[simp]
lemma toWeyl_isotypic_sign (d : SU3PermDecomposition rep V)
    (hstab : ∀ x ∈ d.piece 0, rep gaugeSU3Transp x ∈ d.piece 0) :
    (d.toWeyl hstab).isotypic .sign
      = d.piece 0 ⊓ Module.End.eigenspace (rep gaugeSU3Transp) (-1) := rfl

/-- The standard piece of the upgraded decomposition. -/
@[simp]
lemma toWeyl_isotypic_std (d : SU3PermDecomposition rep V)
    (hstab : ∀ x ∈ d.piece 0, rep gaugeSU3Transp x ∈ d.piece 0) :
    (d.toWeyl hstab).isotypic .std = d.piece 1 ⊔ d.piece 2 := rfl

end SU3PermDecomposition

end StandardModel
