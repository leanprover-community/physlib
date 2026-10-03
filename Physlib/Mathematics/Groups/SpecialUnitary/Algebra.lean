/-
Copyright (c) 2026 Jinzheng Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li
-/
module

public import Mathlib.Algebra.Lie.Basic
public import Mathlib.Algebra.Star.SelfAdjoint
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.Analysis.Complex.Basic
/-!
# The Lie algebra `su(n)` over a `*`-algebra

## i. Overview

The Lie algebra of `SU(n)` is the real Lie algebra of traceless hermitian `n × n` matrices,
with bracket `⁅a, b⁆ = i (a b − b a)` — the factor of `i` keeps the bracket of two hermitian
matrices hermitian. Nothing in this description depends on the entries being complex
numbers: it makes sense over any commutative `*`-algebra `R` over `ℂ`, and the two cases the
theory of jets needs are `R = ℂ` (the Lie algebra itself) and `R` the ring of formal power
series in the spacetime coordinates (its jets). `SUAlgebraOver R n` is this Lie algebra,
together with the conjugation action `a ↦ U a U†` of the unitary group of `R`.

Over `R = ℂ` the Lie algebra is real, since `i` times a hermitian matrix is anti-hermitian. Its
complexification `ℂ ⊗[ℝ] su(n)` is `SUAlgebraComplexified n`, the complex vector space on which
the adjoint representation of `SU(n)` acts in the complex tensors of `SU(n)`.

## ii. Key results

- `SUAlgebraOver` : the traceless hermitian matrices as a real Lie algebra.
- `SUAlgebraOver.conj` : the conjugation representation of the unitary group.
- `SU`, `SUAlgebra` : the group `SU(n)` and its Lie algebra over `ℂ`.
- `SUAlgebraComplexified` : the complexification of `su(n)`.

## iii. Table of contents

- A. Traceless hermitian matrices
- B. The conjugation representation
- C. The bracket
- D. The group `SU(n)` and the complexification

-/

@[expose] public section

open Matrix

/-!

## A. Traceless hermitian matrices

-/

/-- The submodule of traceless hermitian matrices. -/
abbrev SUAlgebraOver.submodule (R : Type) [CommRing R] [StarRing R] [Algebra ℝ R]
    [StarModule ℝ R] (n : ℕ) : Submodule ℝ (Matrix (Fin n) (Fin n) R) :=
  selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) R) ⊓
    LinearMap.ker (Matrix.traceLinearMap (Fin n) ℝ R)

/-- **The Lie algebra `su(n)` over `R`**: traceless hermitian `n × n` matrices with entries in
  `R`, a real Lie algebra with bracket `i (a b − b a)`. -/
abbrev SUAlgebraOver (R : Type) [CommRing R] [StarRing R] [Algebra ℝ R] [StarModule ℝ R]
    (n : ℕ) : Type :=
  ↥(SUAlgebraOver.submodule R n)

namespace SUAlgebraOver

variable {R : Type} [CommRing R] [StarRing R] [Algebra ℝ R] [StarModule ℝ R] {n : ℕ}

lemma mem_iff (A : Matrix (Fin n) (Fin n) R) :
    A ∈ submodule R n ↔ star A = A ∧ A.trace = 0 := Iff.rfl

/-- An element from a traceless hermitian matrix. -/
def ofMatrix (A : Matrix (Fin n) (Fin n) R) (hA : star A = A) (hT : A.trace = 0) :
    SUAlgebraOver R n :=
  ⟨A, hA, hT⟩

@[simp]
lemma ofMatrix_val (A : Matrix (Fin n) (Fin n) R) (hA : star A = A) (hT : A.trace = 0) :
    (ofMatrix A hA hT).1 = A := rfl

lemma star_val (a : SUAlgebraOver R n) : star a.1 = a.1 := a.2.1

lemma trace_val (a : SUAlgebraOver R n) : a.1.trace = 0 := a.2.2

@[ext]
lemma ext {a b : SUAlgebraOver R n} (h : a.1 = b.1) : a = b := Subtype.ext h

/-!

## B. The conjugation representation

-/

/-- **The conjugation representation** of the unitary group on `su(n)`: `a ↦ U a U†`. -/
noncomputable def conj : Representation ℝ (unitaryGroup (Fin n) R) (SUAlgebraOver R n) where
  toFun U :=
    { toFun a := ofMatrix (U.1 * a.1 * star U.1)
        (by rw [star_mul, star_mul, star_star, a.star_val, mul_assoc])
        (by
          rw [Matrix.trace_mul_comm, ← mul_assoc, show star U.1 * U.1 = 1 from
            (Unitary.mem_iff.mp U.2).1, one_mul, a.trace_val])
      map_add' a b := Subtype.ext (by simp [mul_add, add_mul])
      map_smul' r a := Subtype.ext (by simp) }
  map_one' := LinearMap.ext fun a => Subtype.ext (by simp)
  map_mul' U V := LinearMap.ext fun a => Subtype.ext (by simp [star_mul, mul_assoc])

@[simp]
lemma conj_apply_val (U : unitaryGroup (Fin n) R) (a : SUAlgebraOver R n) :
    (conj U a).1 = U.1 * a.1 * star U.1 := rfl

/-!

## C. The bracket

-/

variable [Algebra ℂ R] [StarModule ℂ R]

/-- The bracket `i (a b − b a)`. -/
noncomputable instance : Bracket (SUAlgebraOver R n) (SUAlgebraOver R n) where
  bracket a b := ofMatrix (Complex.I • (a.1 * b.1 - b.1 * a.1))
    (by
      rw [star_smul, star_sub, star_mul, star_mul, a.star_val, b.star_val, Complex.star_def,
        Complex.conj_I, neg_smul, ← smul_neg, neg_sub])
    (by rw [Matrix.trace_smul, Matrix.trace_sub, Matrix.trace_mul_comm, sub_self, smul_zero])

@[simp]
lemma bracket_val (a b : SUAlgebraOver R n) :
    ⁅a, b⁆.1 = Complex.I • (a.1 * b.1 - b.1 * a.1) := rfl

noncomputable instance : LieRing (SUAlgebraOver R n) where
  add_lie a b c := Subtype.ext (by
    simp only [bracket_val, Submodule.coe_add, add_mul, mul_add, smul_add, smul_sub]
    abel)
  lie_add a b c := Subtype.ext (by
    simp only [bracket_val, Submodule.coe_add, add_mul, mul_add, smul_add, smul_sub]
    abel)
  lie_self a := Subtype.ext (by simp)
  leibniz_lie a b c := Subtype.ext (by
    simp only [bracket_val, Submodule.coe_add, mul_smul_comm, smul_mul_assoc, smul_smul,
      Complex.I_mul_I, smul_sub, mul_sub, sub_mul, mul_assoc]
    module)

variable [IsScalarTower ℝ ℂ R]

noncomputable instance : LieAlgebra ℝ (SUAlgebraOver R n) where
  lie_smul r a b := Subtype.ext (by
    ext i j
    simp only [bracket_val, Submodule.coe_smul, Matrix.smul_apply, Matrix.sub_apply,
      Matrix.mul_apply]
    simp only [Algebra.smul_def, mul_sub, Finset.mul_sum]
    congr 1 <;> exact Finset.sum_congr rfl fun k _ => by ring)

end SUAlgebraOver

/-!

## D. The group `SU(n)` and the complexification

-/

/-- The group `SU(n)` of special unitary complex `n × n` matrices. -/
abbrev SU (n : ℕ) : Type := specialUnitaryGroup (Fin n) ℂ

/-- The Lie algebra `su(n)`: traceless hermitian complex `n × n` matrices. -/
abbrev SUAlgebra (n : ℕ) : Type := SUAlgebraOver ℂ n

open TensorProduct in
/-- **The complexified Lie algebra `su(n)_ℂ = ℂ ⊗[ℝ] su(n)`**, a complex vector space. -/
abbrev SUAlgebraComplexified (n : ℕ) : Type := ℂ ⊗[ℝ] SUAlgebraOver ℂ n
