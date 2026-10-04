/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import Mathlib.Algebra.Lie.Basic
public import Mathlib.Algebra.Star.SelfAdjoint
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.Analysis.Complex.Basic
/-!

# The Lie algebra `su(n)` in the hermitian presentation

## i. Overview

In physics, `su(n)` is described through generators `T^a`, `a = 1, …, n² - 1`, a basis of the
traceless hermitian `n × n` complex matrices, satisfying `[T^a, T^b] = i f_{abc} T^c` with real
structure constants `f_{abc}`. Here `i` is the imaginary unit and the repeated index `c` is summed.
This file makes the traceless hermitian matrices into a real Lie algebra with the bracket
`⁅x, y⁆ = i (x y - y x)`, on which the unitary group acts by conjugation. The construction allows
entries in any commutative `*`-ring `R` that is both a real and a complex `*`-algebra, as
`SUAlgebra n R`; the Lie algebra `su(n)` itself is `SUAlgebra n ℂ`.

## ii. Key results

- `SUAlgebra n R` : traceless hermitian `n × n` matrices over `R`, as a real Lie algebra.
- `SUAlgebra.conj` : the representation `x ↦ U x U†` of the unitary group.
- `SUAlgebra.conj_lie` : conjugation by a unitary matrix preserves the bracket.

## iii. Table of contents

- A. Traceless hermitian matrices
- B. The conjugation representation
- C. The bracket
- D. Conjugation preserves the bracket

-/

@[expose] public section

open Matrix

/-!

## A. Traceless hermitian matrices

Since `i A` is skew-hermitian when `A` is hermitian, the traceless hermitian matrices form a real
vector space.

-/

/-- The traceless hermitian `n × n` matrices with entries in `R`, as a real subspace. -/
abbrev SUAlgebra.submodule (n : ℕ) (R : Type*) [CommRing R] [StarRing R] [Algebra ℝ R]
    [StarModule ℝ R] : Submodule ℝ (Matrix (Fin n) (Fin n) R) :=
  selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) R) ⊓
    LinearMap.ker (Matrix.traceLinearMap (Fin n) ℝ R)

/-- Traceless hermitian `n × n` matrices with entries in `R`, as a real Lie algebra;
  `SUAlgebra n ℂ` is `su(n)`. -/
abbrev SUAlgebra (n : ℕ) (R : Type*) [CommRing R] [StarRing R] [Algebra ℝ R]
    [StarModule ℝ R] : Type _ :=
  ↥(SUAlgebra.submodule n R)

namespace SUAlgebra

variable {n : ℕ} {R : Type*} [CommRing R] [StarRing R] [Algebra ℝ R] [StarModule ℝ R]

/-- The element given by a traceless hermitian matrix. -/
def ofMatrix (A : Matrix (Fin n) (Fin n) R) (hA : star A = A) (hT : A.trace = 0) :
    SUAlgebra n R :=
  ⟨A, hA, hT⟩

/-- The underlying matrix of `ofMatrix A hA hT` is `A`. -/
@[simp]
lemma ofMatrix_val (A : Matrix (Fin n) (Fin n) R) (hA : star A = A) (hT : A.trace = 0) :
    (ofMatrix A hA hT).1 = A := rfl

/-- The underlying matrix of an element is hermitian. -/
lemma star_val_eq (x : SUAlgebra n R) : star x.1 = x.1 := x.2.1

/-- The underlying matrix of an element is traceless. -/
lemma trace_val_eq_zero (x : SUAlgebra n R) : x.1.trace = 0 := x.2.2

/-!

## B. The conjugation representation

Conjugation `x ↦ U x U†` by a unitary matrix `U` preserves traceless hermitian matrices, by
`U† U = 1` and cyclicity of the trace, and defines a representation of the unitary group.

-/

/-- The conjugation representation of the unitary group on `SUAlgebra n R`: `x ↦ U x U†`. -/
noncomputable def conj : Representation ℝ (unitaryGroup (Fin n) R) (SUAlgebra n R) where
  toFun U :=
    { toFun x := ofMatrix (U.1 * x.1 * star U.1)
        (by rw [star_mul, star_mul, star_star, x.star_val_eq, mul_assoc])
        (by
          rw [Matrix.trace_mul_comm, ← mul_assoc, UnitaryGroup.star_mul_self U, one_mul,
            x.trace_val_eq_zero])
      map_add' x y := Subtype.ext (by simp [mul_add, add_mul])
      map_smul' r x := Subtype.ext (by simp) }
  map_one' := LinearMap.ext fun x => Subtype.ext (by simp)
  map_mul' U V := LinearMap.ext fun x => Subtype.ext (by simp [star_mul, mul_assoc])

/-- The underlying matrix of `conj U x` is `U x U†`. -/
@[simp]
lemma conj_apply_val (U : unitaryGroup (Fin n) R) (x : SUAlgebra n R) :
    (conj U x).1 = U.1 * x.1 * star U.1 := rfl

/-!

## C. The bracket

From here on `R` is also a complex `*`-algebra, so that matrices can be multiplied by `i`. The
commutator of two hermitian matrices is skew-hermitian, and multiplying it by `i` makes it
hermitian again, giving the bracket `⁅x, y⁆ = i (x y - y x)`. Being `i` times the commutator, it
is a Lie bracket.

Since `[i x, i y] = i ⁅x, y⁆`, multiplication by `i` turns this bracket into the commutator of
traceless skew-hermitian matrices, the usual mathematical presentation of `su(n)`.

The factor `i` flips the sign of the structure constants; if `[T^a, T^b] = i f_{abc} T^c`, then
`⁅T^a, T^b⁆ = -f_{abc} T^c`.

-/

variable [Algebra ℂ R] [StarModule ℂ R]

/-- The bracket `⁅x, y⁆ = i (x y - y x)`. -/
noncomputable instance : Bracket (SUAlgebra n R) (SUAlgebra n R) where
  bracket x y := ofMatrix (Complex.I • (x.1 * y.1 - y.1 * x.1))
    (by
      rw [star_smul, star_sub, star_mul, star_mul, x.star_val_eq, y.star_val_eq,
        Complex.star_def, Complex.conj_I, neg_smul, ← smul_neg, neg_sub])
    (by rw [Matrix.trace_smul, Matrix.trace_sub, Matrix.trace_mul_comm, sub_self, smul_zero])

/-- The underlying matrix of `⁅x, y⁆` is `i (x y - y x)`. -/
@[simp]
lemma bracket_val (x y : SUAlgebra n R) :
    ⁅x, y⁆.1 = Complex.I • (x.1 * y.1 - y.1 * x.1) := rfl

/-- `⁅x, y⁆ = i (x y - y x)` makes `SUAlgebra n R` a Lie ring. -/
noncomputable instance : LieRing (SUAlgebra n R) where
  add_lie x y z := Subtype.ext (by
    simp only [bracket_val, Submodule.coe_add, add_mul, mul_add, smul_add, smul_sub]
    abel)
  lie_add x y z := Subtype.ext (by
    simp only [bracket_val, Submodule.coe_add, add_mul, mul_add, smul_add, smul_sub]
    abel)
  lie_self x := Subtype.ext (by simp)
  leibniz_lie x y z := Subtype.ext (by
    simp only [bracket_val, Submodule.coe_add, mul_smul_comm, smul_mul_assoc, smul_smul,
      Complex.I_mul_I, smul_sub, mul_sub, sub_mul, mul_assoc]
    module)

/-- The bracket is `ℝ`-bilinear, so `SUAlgebra n R` is a real Lie algebra. -/
noncomputable instance : LieAlgebra ℝ (SUAlgebra n R) where
  lie_smul r x y := Subtype.ext (by
    ext i j
    simp only [bracket_val, Submodule.coe_smul, Matrix.smul_apply, Matrix.sub_apply,
      Matrix.mul_apply]
    simp only [Algebra.smul_def, mul_sub, Finset.mul_sum]
    congr 1 <;> exact Finset.sum_congr rfl fun k _ => by ring)

/-!

## D. Conjugation preserves the bracket

-/

/-- Conjugation by a unitary matrix preserves the bracket, so `conj` acts by Lie algebra
  automorphisms. -/
lemma conj_lie (U : unitaryGroup (Fin n) R) (x y : SUAlgebra n R) :
    conj U ⁅x, y⁆ = ⁅conj U x, conj U y⁆ := by
  ext1
  simp only [conj_apply_val, bracket_val, Matrix.mul_smul, Matrix.smul_mul, mul_sub, sub_mul]
  congr 2 <;> simp only [mul_assoc, ← mul_assoc (star U.1) U.1, UnitaryGroup.star_mul_self,
    one_mul]

end SUAlgebra
