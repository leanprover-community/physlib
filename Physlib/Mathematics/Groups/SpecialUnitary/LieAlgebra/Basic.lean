/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import Mathlib.Algebra.Lie.BaseChange
public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.RepresentationTheory.Basic
/-!

# The Lie algebra `su(n)` in the hermitian presentation

## i. Overview

In physics, `su(n)` is described through generators `T^a`, `a = 1, …, n² - 1`, a basis of the
traceless hermitian `n × n` complex matrices, satisfying `[T^a, T^b] = i f_{abc} T^c` with real
structure constants `f_{abc}`. Here `i` is the imaginary unit and the repeated index `c` is summed.
This file makes the traceless hermitian matrices into a real Lie algebra with the bracket
`⁅x, y⁆ = i (x y - y x)`, on which the unitary group acts by conjugation. The construction allows
entries in any commutative `*`-ring `R` that is both a real and a complex `*`-algebra, as
`SULieAlgebra n R`; the Lie algebra `su(n)` itself is `SULieAlgebra n ℂ`.

Sending `z ⊗ x` to the matrix `z x` identifies the complexification `ℂ ⊗[ℝ] su(n)` with the
traceless complex matrices. The inverse writes a traceless matrix `M` as `ℜ M + i ℑ M`, its real
and imaginary parts `ℜ M` and `ℑ M` being traceless hermitian.

## ii. Key results

- `SULieAlgebra n R` : traceless hermitian `n × n` matrices over `R`, as a real Lie algebra.
- `SULieAlgebra.conj` : the representation `x ↦ U x U†` of the unitary group.
- `SULieAlgebra.conj_lie` : conjugation by a unitary matrix preserves the bracket.
- `SULieAlgebra.Complexification n` : the complexification `ℂ ⊗[ℝ] su(n)`.
- `SULieAlgebra.toMatrixℂ` : the underlying matrix of an element of the complexification.
- `SULieAlgebra.toMatrixℂ_lie` : the matrix of a bracket is `i` times the commutator.
- `SULieAlgebra.toMatrixℂ_injective`, `SULieAlgebra.range_toMatrixℂ` : the complexification is
  the traceless complex matrices.
- `SULieAlgebra.equivTraceKer` : the linear equivalence between the complexification and the
  traceless complex matrices.
- `SULieAlgebra.finrank_eq`, `SULieAlgebra.finrank_complexification` : `su(n)` and its
  complexification have dimension `n² - 1`.

## iii. Table of contents

- A. Traceless hermitian matrices
- B. The conjugation representation
- C. The bracket
- D. Conjugation preserves the bracket
- E. The complexification
  - E.1. The underlying matrix of the complexification
  - E.2. The element with a given traceless matrix
  - E.3. The injectivity and surjectivity of the matrix map
  - E.4. Commuting with all elements of `su(n)`
  - E.5. Linear equivalences
- F. The dimension

## iv. References

* None.

-/

@[expose] public section

open Matrix TensorProduct ComplexStarModule

/-!

## A. Traceless hermitian matrices

Since `i A` is skew-hermitian when `A` is hermitian, the traceless hermitian matrices form a real
vector space.

-/

/-- The traceless hermitian `n × n` matrices with entries in `R`, as a real subspace. -/
abbrev SULieAlgebra.submodule (n : ℕ) (R : Type*) [CommRing R] [StarRing R] [Algebra ℝ R]
    [StarModule ℝ R] : Submodule ℝ (Matrix (Fin n) (Fin n) R) :=
  selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) R) ⊓
    LinearMap.ker (Matrix.traceLinearMap (Fin n) ℝ R)

/-- Traceless hermitian `n × n` matrices with entries in `R`, as a real Lie algebra;
  `SULieAlgebra n ℂ` is `su(n)`. -/
abbrev SULieAlgebra (n : ℕ) (R : Type*) [CommRing R] [StarRing R] [Algebra ℝ R]
    [StarModule ℝ R] : Type _ :=
  ↥(SULieAlgebra.submodule n R)

namespace SULieAlgebra

variable {n : ℕ} {R : Type*} [CommRing R] [StarRing R] [Algebra ℝ R] [StarModule ℝ R]

/-- The element given by a traceless hermitian matrix. -/
def ofMatrix (A : Matrix (Fin n) (Fin n) R) (hA : star A = A) (hT : A.trace = 0) :
    SULieAlgebra n R := ⟨A, hA, hT⟩

/-- The underlying matrix of `ofMatrix A hA hT` is `A`. -/
@[simp]
lemma val_ofMatrix (A : Matrix (Fin n) (Fin n) R) (hA : star A = A) (hT : A.trace = 0) :
    (ofMatrix A hA hT).1 = A := rfl

/-- The underlying matrix of an element is hermitian. -/
lemma star_val_eq (x : SULieAlgebra n R) : star x.1 = x.1 := x.2.1

/-- The underlying matrix of an element is traceless. -/
lemma trace_val_eq_zero (x : SULieAlgebra n R) : x.1.trace = 0 := x.2.2

/-!

## B. The conjugation representation

Conjugation `x ↦ U x U†` by a unitary matrix `U` preserves traceless hermitian matrices, by
`U† U = 1` and cyclicity of the trace, and defines a representation of the unitary group.

-/

/-- The conjugation representation of the unitary group on `SULieAlgebra n R`: `x ↦ U x U†`. -/
noncomputable def conj : Representation ℝ (unitaryGroup (Fin n) R) (SULieAlgebra n R) where
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
lemma val_conj_apply (U : unitaryGroup (Fin n) R) (x : SULieAlgebra n R) :
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
noncomputable instance : Bracket (SULieAlgebra n R) (SULieAlgebra n R) where
  bracket x y := ofMatrix (Complex.I • (x.1 * y.1 - y.1 * x.1))
    (by
      rw [star_smul, star_sub, star_mul, star_mul, x.star_val_eq, y.star_val_eq,
        Complex.star_def, Complex.conj_I, neg_smul, ← smul_neg, neg_sub])
    (by rw [Matrix.trace_smul, Matrix.trace_sub, Matrix.trace_mul_comm, sub_self, smul_zero])

/-- The underlying matrix of `⁅x, y⁆` is `i (x y - y x)`. -/
@[simp]
lemma val_bracket (x y : SULieAlgebra n R) :
    ⁅x, y⁆.1 = Complex.I • (x.1 * y.1 - y.1 * x.1) := rfl

/-- `⁅x, y⁆ = i (x y - y x)` makes `SULieAlgebra n R` a Lie ring. -/
noncomputable instance : LieRing (SULieAlgebra n R) where
  add_lie x y z := Subtype.ext (by
    simp only [val_bracket, Submodule.coe_add, add_mul, mul_add, smul_add, smul_sub]
    abel)
  lie_add x y z := Subtype.ext (by
    simp only [val_bracket, Submodule.coe_add, add_mul, mul_add, smul_add, smul_sub]
    abel)
  lie_self x := Subtype.ext (by simp)
  leibniz_lie x y z := Subtype.ext (by
    simp only [val_bracket, Submodule.coe_add, mul_smul_comm, smul_mul_assoc, smul_smul,
      Complex.I_mul_I, smul_sub, mul_sub, sub_mul, mul_assoc]
    module)

/-- The bracket is `ℝ`-bilinear, so `SULieAlgebra n R` is a real Lie algebra. -/
noncomputable instance : LieAlgebra ℝ (SULieAlgebra n R) where
  lie_smul r x y := Subtype.ext (by
    ext i j
    simp only [val_bracket, Submodule.coe_smul, Matrix.smul_apply, Matrix.sub_apply,
      Matrix.mul_apply]
    simp only [Algebra.smul_def, mul_sub, Finset.mul_sum]
    congr 1 <;> exact Finset.sum_congr rfl fun k _ => by ring)

/-!

## D. Conjugation preserves the bracket

-/

/-- Conjugation by a unitary matrix preserves the bracket, so `conj` acts by Lie algebra
  automorphisms. -/
lemma conj_lie (U : unitaryGroup (Fin n) R) (x y : SULieAlgebra n R) :
    conj U ⁅x, y⁆ = ⁅conj U x, conj U y⁆ := by
  ext1
  simp only [val_conj_apply, val_bracket, Matrix.mul_smul, Matrix.smul_mul, mul_sub, sub_mul]
  congr 2 <;> simp only [mul_assoc, ← mul_assoc (star U.1) U.1, UnitaryGroup.star_mul_self,
    one_mul]

/-!

## E. The complexification

-/

/-- The complexification `ℂ ⊗[ℝ] su(n)` of `su(n)`, a complex Lie algebra. -/
abbrev Complexification (n : ℕ) : Type := ℂ ⊗[ℝ] SULieAlgebra n ℂ

/-!

### E.1. The underlying matrix of the complexification

-/

/-- The underlying matrix of an element of the complexification, `z ⊗ x ↦ z x`. -/
noncomputable def toMatrixℂ : Complexification n →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ :=
  (SULieAlgebra.submodule n ℂ).subtype.liftBaseChange ℂ

@[simp]
lemma toMatrixℂ_tmul (z : ℂ) (x : SULieAlgebra n ℂ) : toMatrixℂ (z ⊗ₜ x) = z • x.1 := rfl

/-- The underlying matrix of an element of the complexification is traceless. -/
lemma trace_toMatrixℂ (A : Complexification n) : (toMatrixℂ A).trace = 0 := by
  induction A using TensorProduct.inductionOn with
  | tmul z x => rw [toMatrixℂ_tmul, Matrix.trace_smul, x.trace_val_eq_zero, smul_zero]
  | add A B hA hB => rw [map_add, Matrix.trace_add, hA, hB, add_zero]

/-- The matrix of a bracket is `i` times the commutator of the matrices, `[A, B] ↦ i (A B - B A)`,
  as in `su(n)` itself. -/
lemma toMatrixℂ_lie (A B : Complexification n) :
    toMatrixℂ ⁅A, B⁆ = Complex.I • (toMatrixℂ A * toMatrixℂ B - toMatrixℂ B * toMatrixℂ A) := by
  induction A using TensorProduct.inductionOn with
  | tmul z x =>
    induction B using TensorProduct.inductionOn with
    | tmul w y =>
      rw [LieAlgebra.ExtendScalars.bracket_tmul, toMatrixℂ_tmul, toMatrixℂ_tmul, toMatrixℂ_tmul,
        val_bracket]
      simp only [Matrix.smul_mul, Matrix.mul_smul]
      module
    | add B B' hB hB' =>
      rw [lie_add (L := Complexification n), map_add, hB, hB', map_add, Matrix.mul_add,
        Matrix.add_mul]
      module
  | add A A' hA hA' =>
    rw [add_lie (L := Complexification n), map_add, hA, hA', map_add, Matrix.mul_add,
      Matrix.add_mul]
    module

/-!

### E.2. The element with a given traceless matrix

-/

/-- The element `1 ⊗ ℜ M + i ⊗ ℑ M` of the complexification with the traceless matrix `M`. -/
noncomputable def ofTracelessℂ (M : Matrix (Fin n) (Fin n) ℂ) (hM : M.trace = 0) :
    Complexification n :=
  1 ⊗ₜ ofMatrix (ℜ M) (selfAdjoint.mem_iff.mp (ℜ M).2) (by
      simp [realPart_apply_coe, trace_smul, trace_add, star_eq_conjTranspose,
        trace_conjTranspose, hM]) +
    Complex.I ⊗ₜ ofMatrix (ℑ M) (selfAdjoint.mem_iff.mp (ℑ M).2) (by
      simp [imaginaryPart_apply_coe, trace_smul, trace_sub, star_eq_conjTranspose,
        trace_conjTranspose, hM])

/-- The matrix of `ofTracelessℂ M` is `M = ℜ M + i ℑ M`. -/
@[simp]
lemma toMatrixℂ_ofTracelessℂ (M : Matrix (Fin n) (Fin n) ℂ) (hM : M.trace = 0) :
    toMatrixℂ (ofTracelessℂ M hM) = M := by
  rw [ofTracelessℂ, map_add, toMatrixℂ_tmul, toMatrixℂ_tmul, one_smul, val_ofMatrix,
    val_ofMatrix, realPart_add_I_smul_imaginaryPart]

/-- `ofTracelessℂ` is additive. -/
lemma ofTracelessℂ_add (M N : Matrix (Fin n) (Fin n) ℂ) (hM : M.trace = 0) (hN : N.trace = 0)
    (hMN : (M + N).trace = 0) :
    ofTracelessℂ (M + N) hMN = ofTracelessℂ M hM + ofTracelessℂ N hN := by
  rw [ofTracelessℂ, ofTracelessℂ, ofTracelessℂ, add_add_add_comm, ← tmul_add, ← tmul_add]
  congr 2 <;> exact Subtype.ext (by simp)

/-- An element of the complexification is recovered from its matrix. -/
@[simp]
lemma ofTracelessℂ_toMatrixℂ (A : Complexification n) :
    ofTracelessℂ (toMatrixℂ A) (trace_toMatrixℂ A) = A := by
  induction A using TensorProduct.inductionOn with
  | tmul z x =>
    have hre : ∀ h₁ h₂, ofMatrix (ℜ (z • x.1)) h₁ h₂ = z.re • x := fun _ _ => Subtype.ext (by
      simp [realPart_smul, IsSelfAdjoint.coe_realPart x.star_val_eq,
        IsSelfAdjoint.imaginaryPart x.star_val_eq])
    have him : ∀ h₁ h₂, ofMatrix (ℑ (z • x.1)) h₁ h₂ = z.im • x := fun _ _ => Subtype.ext (by
      simp [imaginaryPart_smul, IsSelfAdjoint.coe_realPart x.star_val_eq,
        IsSelfAdjoint.imaginaryPart x.star_val_eq])
    rw [ofTracelessℂ]
    simp only [toMatrixℂ_tmul, hre, him]
    rw [← smul_tmul, ← smul_tmul, ← add_tmul, Complex.real_smul, Complex.real_smul, mul_one,
      Complex.re_add_im]
  | add A B hA hB =>
    calc _ = ofTracelessℂ (toMatrixℂ A + toMatrixℂ B)
          (by rw [← map_add]; exact trace_toMatrixℂ _) := by
          congr 1
          exact map_add _ _ _
      _ = A + B := by rw [ofTracelessℂ_add _ _ (trace_toMatrixℂ A) (trace_toMatrixℂ B), hA, hB]

/-!

### E.3. The injectivity and surjectivity of the matrix map

-/

/-- An element of the complexification is determined by its matrix. -/
lemma toMatrixℂ_injective : Function.Injective (toMatrixℂ (n := n)) := fun A B h => by
  rw [← ofTracelessℂ_toMatrixℂ A, ← ofTracelessℂ_toMatrixℂ B]
  congr 1

/-- The matrices of elements of the complexification are exactly the traceless matrices. -/
lemma range_toMatrixℂ :
    LinearMap.range (toMatrixℂ (n := n)) = LinearMap.ker (Matrix.traceLinearMap (Fin n) ℂ ℂ) := by
  ext M
  rw [LinearMap.mem_range, LinearMap.mem_ker, Matrix.traceLinearMap_apply]
  exact ⟨fun ⟨A, hA⟩ => hA ▸ trace_toMatrixℂ A,
    fun hM => ⟨ofTracelessℂ M hM, toMatrixℂ_ofTracelessℂ M hM⟩⟩

/-!

### E.4. Commuting with all elements of `su(n)`

-/

/-- A matrix commuting with every element of `su(n)` commutes with every matrix: it commutes with
  the traceless matrices, which `su(n)` spans over `ℂ`, and with the identity. -/
lemma commute_of_forall_commute_val {M : Matrix (Fin n) (Fin n) ℂ}
    (h : ∀ x : SULieAlgebra n ℂ, Commute M x.1) (N : Matrix (Fin n) (Fin n) ℂ) : Commute M N := by
  have hA (A : Complexification n) : Commute M (toMatrixℂ A) := by
    induction A using TensorProduct.inductionOn with
    | tmul z x => exact toMatrixℂ_tmul z x ▸ (h x).smul_right z
    | add A B hA hB => exact map_add toMatrixℂ A B ▸ hA.add_right hB
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact Subsingleton.elim (M * N) (N * M)
  have hN : (N - (N.trace / n) • (1 : Matrix (Fin n) (Fin n) ℂ)).trace = 0 := by
    rw [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, smul_eq_mul,
      div_mul_cancel₀ _ (by exact_mod_cast hn.ne'), sub_self]
  have h1 := toMatrixℂ_ofTracelessℂ _ hN ▸ hA (ofTracelessℂ _ hN)
  simpa using h1.add_right ((Commute.one_right M).smul_right (N.trace / n))

/-!

### E.5. Linear equivalences

-/

/-- The linear equivalence between the complexification of `su(n)` and the traceless complex
  matrices, sending an element to its matrix. -/
noncomputable def equivTraceKer :
    Complexification n ≃ₗ[ℂ] LinearMap.ker (Matrix.traceLinearMap (Fin n) ℂ ℂ) where
  toFun A := ⟨toMatrixℂ A, trace_toMatrixℂ A⟩
  invFun M := ofTracelessℂ M.1 M.2
  map_add' A B := Subtype.ext (map_add _ A B)
  map_smul' z A := Subtype.ext (map_smul _ z A)
  left_inv := ofTracelessℂ_toMatrixℂ
  right_inv _ := Subtype.ext (toMatrixℂ_ofTracelessℂ _ _)

/-- The matrix of `equivTraceKer A` is the matrix of `A`. -/
@[simp]
lemma val_equivTraceKer (A : Complexification n) : (equivTraceKer A).1 = toMatrixℂ A := rfl

/-- The matrix of `equivTraceKer.symm M` is `M`. -/
@[simp]
lemma toMatrixℂ_equivTraceKer_symm (M : LinearMap.ker (traceLinearMap (Fin n) ℂ ℂ)) :
    toMatrixℂ (equivTraceKer.symm M) = M.1 := toMatrixℂ_ofTracelessℂ _ M.2

/-!

## F. The dimension

-/

/-- The complexification `ℂ ⊗[ℝ] su(n)` has complex dimension `n² - 1`: it is the traceless
  matrices, and the trace is onto for `0 < n`. -/
lemma finrank_complexification : Module.finrank ℂ (Complexification n) = n ^ 2 - 1 := by
  rw [← LinearMap.finrank_range_of_inj toMatrixℂ_injective, range_toMatrixℂ]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact Module.finrank_zero_of_subsingleton
  have hsurj : LinearMap.range (Matrix.traceLinearMap (Fin n) ℂ ℂ) = ⊤ :=
    LinearMap.range_eq_top.2 fun c => ⟨single ⟨0, hn⟩ ⟨0, hn⟩ c, by simp⟩
  have h := LinearMap.finrank_range_add_finrank_ker (Matrix.traceLinearMap (Fin n) ℂ ℂ)
  rw [hsurj, finrank_top, Module.finrank_matrix, Fintype.card_fin, Module.finrank_self] at h
  rw [sq]
  omega

/-- `su(n)` has real dimension `n² - 1`, the dimension of its complexification. -/
lemma finrank_eq : Module.finrank ℝ (SULieAlgebra n ℂ) = n ^ 2 - 1 := by
  rw [← Module.finrank_baseChange (R := ℂ)]
  exact finrank_complexification

end SULieAlgebra
