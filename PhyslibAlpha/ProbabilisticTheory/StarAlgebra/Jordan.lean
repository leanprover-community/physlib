/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Mathlib.Algebra.Jordan.Basic
public import Mathlib.Tactic.NoncommRing
public import PhyslibAlpha.ProbabilisticTheory.StarAlgebra.Observable

/-!

# The Jordan product of observables

## i. Overview

The product of two self-adjoint elements is self-adjoint only when they commute, but the symmetrized
product `a ∘ b = ½ (a b + b a)` is always self-adjoint. It is commutative and satisfies the Jordan
identity, so the observables form a Jordan algebra. The product is a scoped instance on `selfAdjoint
A`, since for commutative `A` Mathlib already gives `selfAdjoint A` the ordinary product.

## ii. Key results

- `selfAdjoint.jordanMul` : the Jordan product `½ (a b + b a)`.
- `selfAdjoint.jordanMul_comm` : the Jordan product is commutative.
- `selfAdjoint.jordanMul_jordanMul_jordanMul_self` : the Jordan identity.

-/

@[expose] public section

namespace selfAdjoint
open ProbabilisticTheory

variable {A : Type*} [Ring A] [StarRing A] [Module ℝ A] [StarModule ℝ A]

/-- The unnormalized anticommutator, retained as a low-level formula while `jordanMul` is the
canonical normalized Jordan product. -/
def anticommutator (a b : selfAdjoint A) : selfAdjoint A :=
  ⟨(a : A) * (b : A) + (b : A) * (a : A), by
    rw [mem_iff, star_add, star_mul, star_mul, star_val_eq, star_val_eq, add_comm]⟩

omit [Module ℝ A] [StarModule ℝ A] in
@[simp]
lemma coe_anticommutator (a b : selfAdjoint A) :
    ((anticommutator a b : selfAdjoint A) : A) = (a : A) * (b : A) + (b : A) * (a : A) :=
  rfl

/-- The normalized Jordan product of two self-adjoint elements,
`a ∘ b := ½(ab + ba)`. It is self-adjoint regardless of whether `a` and `b` commute, since
`star (a * b + b * a) = star b * star a + star a * star b = b * a + a * b`. -/
noncomputable def jordanMul (a b : selfAdjoint A) : selfAdjoint A :=
  (2 : ℝ)⁻¹ • anticommutator a b

@[simp]
lemma val_jordanMul (a b : selfAdjoint A) :
    ((jordanMul a b : selfAdjoint A) : A) =
      (2 : ℝ)⁻¹ • ((a : A) * (b : A) + (b : A) * (a : A)) :=
  rfl

/-- The Jordan product is commutative. -/
lemma jordanMul_comm (a b : selfAdjoint A) : jordanMul a b = jordanMul b a :=
  Subtype.ext <| by simp only [val_jordanMul, add_comm]

/-- The unit of the ambient algebra is a unit for the normalized Jordan product. -/
@[simp]
lemma one_jordanMul (a : selfAdjoint A) : jordanMul 1 a = a := by
  apply Subtype.ext
  change (2 : ℝ)⁻¹ • ((1 : A) * (a : A) + (a : A) * (1 : A)) = (a : A)
  rw [_root_.one_mul, _root_.mul_one, ← two_smul ℝ (a : A), smul_smul,
    inv_mul_cancel₀ (two_ne_zero), one_smul]

/-- The normalized Jordan product has the same unit in its right argument. -/
@[simp]
lemma jordanMul_one (a : selfAdjoint A) : jordanMul a 1 = a := by
  rw [jordanMul_comm, one_jordanMul]

/-- The Jordan product distributes over addition in its right argument. -/
lemma jordanMul_add_right (a b c : selfAdjoint A) :
    jordanMul a (b + c) = jordanMul a b + jordanMul a c := by
  apply Subtype.ext
  simp only [val_jordanMul, AddSubgroup.coe_add, mul_add, add_mul, smul_add]
  module

/-- The Jordan product distributes over addition in its left argument. -/
lemma jordanMul_add_left (a b c : selfAdjoint A) :
    jordanMul (a + b) c = jordanMul a c + jordanMul b c := by
  rw [jordanMul_comm (a + b) c, jordanMul_comm a c, jordanMul_comm b c]
  exact jordanMul_add_right c a b

lemma anticommutator_smul_left [SMulCommClass ℝ A A] [IsScalarTower ℝ A A]
    (c : ℝ) (a b : selfAdjoint A) :
    anticommutator (c • a) b = c • anticommutator a b := by
  apply Subtype.ext
  simp only [coe_anticommutator, val_smul, mul_smul_comm, smul_mul_assoc, smul_add]

lemma anticommutator_smul_right [SMulCommClass ℝ A A] [IsScalarTower ℝ A A]
    (a : selfAdjoint A) (c : ℝ) (b : selfAdjoint A) :
    anticommutator a (c • b) = c • anticommutator a b := by
  apply Subtype.ext
  simp only [coe_anticommutator, val_smul, mul_smul_comm, smul_mul_assoc, smul_add]

omit [Module ℝ A] [StarModule ℝ A] in
lemma anticommutator_identity (a b : selfAdjoint A) :
    anticommutator (anticommutator a b) (anticommutator a a) =
      anticommutator a (anticommutator b (anticommutator a a)) := by
  apply Subtype.ext
  simp only [coe_anticommutator]
  noncomm_ring

/-- The Jordan identity: `∘`-multiplication by `a` and by `a ∘ a` commute, i.e.
`(a ∘ b) ∘ (a ∘ a) = a ∘ (b ∘ (a ∘ a))`. This is the "weak associativity" law that survives
symmetrization of a possibly non-commutative, associative product. -/
lemma jordanMul_jordanMul_jordanMul_self [SMulCommClass ℝ A A] [IsScalarTower ℝ A A]
    (a b : selfAdjoint A) :
    jordanMul (jordanMul a b) (jordanMul a a) = jordanMul a (jordanMul b (jordanMul a a)) := by
  simp only [jordanMul, anticommutator_smul_left, anticommutator_smul_right, smul_smul]
  congr 1
  exact anticommutator_identity a b

/-- The Jordan product as a scoped multiplication on `selfAdjoint A`. -/
noncomputable scoped instance instMul : Mul (selfAdjoint A) := ⟨jordanMul⟩

@[simp]
lemma mul_def (a b : selfAdjoint A) : a * b = jordanMul a b := rfl

/-- Coercing the canonical Jordan product back to the ambient algebra gives the normalized
anticommutator. -/
lemma coe_mul (a b : selfAdjoint A) :
    ((a * b : selfAdjoint A) : A) =
      (2 : ℝ)⁻¹ • ((a : A) * (b : A) + (b : A) * (a : A)) :=
  val_jordanMul a b

/-- Real scalars pull out of the left argument of the normalized Jordan product. -/
lemma jordanMul_smul_left [SMulCommClass ℝ A A] [IsScalarTower ℝ A A]
    (c : ℝ) (a b : selfAdjoint A) : jordanMul (c • a) b = c • jordanMul a b := by
  apply Subtype.ext
  simp only [val_jordanMul, val_smul, mul_smul_comm, smul_mul_assoc, smul_add, smul_smul]
  module

/-- Real scalars pull out of the right argument of the normalized Jordan product. -/
lemma jordanMul_smul_right [SMulCommClass ℝ A A] [IsScalarTower ℝ A A]
    (a : selfAdjoint A) (c : ℝ) (b : selfAdjoint A) :
    jordanMul a (c • b) = c • jordanMul a b := by
  rw [jordanMul_comm, jordanMul_smul_left, jordanMul_comm]

/-- Expanding one right-nested Jordan product produces a common factor `1 / 4` and a nested
unnormalized anticommutator. This is useful for associative calculations in concrete
realizations while keeping the normalized Jordan product canonical. -/
lemma jordanMul_jordanMul_right [SMulCommClass ℝ A A] [IsScalarTower ℝ A A]
    (a b x : selfAdjoint A) :
    jordanMul a (jordanMul b x) =
      ((2 : ℝ)⁻¹ * (2 : ℝ)⁻¹) • anticommutator a (anticommutator b x) := by
  simp only [jordanMul, anticommutator_smul_right, smul_smul]

section AlgebraStructure

variable [SMulCommClass ℝ A A] [IsScalarTower ℝ A A]

omit [SMulCommClass ℝ A A] [IsScalarTower ℝ A A] in
lemma jordanMul_zero (a : selfAdjoint A) : jordanMul a 0 = 0 := by
  apply Subtype.ext
  simp [val_jordanMul]

/-- The normalized product gives the self-adjoint part its canonical commutative,
nonassociative ring structure. -/
noncomputable scoped instance instNonUnitalNonAssocCommRing :
    NonUnitalNonAssocCommRing (selfAdjoint A) where
  __ := (inferInstance : AddCommGroup (selfAdjoint A))
  mul := jordanMul
  left_distrib := jordanMul_add_right
  right_distrib := jordanMul_add_left
  zero_mul a := (jordanMul_comm 0 a).trans (jordanMul_zero a)
  mul_zero := jordanMul_zero
  mul_comm := jordanMul_comm

/-- The canonical Jordan product is unital with the inherited self-adjoint unit. Bundling this as
`NonAssocCommRing` prevents stronger layers from carrying an unrelated `One` plus duplicated unit
laws. -/
noncomputable scoped instance instNonAssocRing : NonAssocRing (selfAdjoint A) :=
  NonAssocRing.mk (toNatCast := ⟨fun n => n • (1 : selfAdjoint A)⟩)
    (toIntCast := ⟨fun z => z • (1 : selfAdjoint A)⟩)
    one_jordanMul jordanMul_one
    (natCast_zero := by simp)
    (natCast_succ := by intro n; simp [add_nsmul])
    (intCast_ofNat := by
      intro n
      change (n : ℤ) • (1 : selfAdjoint A) = n • (1 : selfAdjoint A)
      simp)
    (intCast_negSucc := by
      intro n
      change (Int.negSucc n) • (1 : selfAdjoint A) = -((n + 1) • (1 : selfAdjoint A))
      simp)

/-- The coherent unital commutative nonassociative ring structure on the self-adjoint part. -/
noncomputable scoped instance instNonAssocCommRing : NonAssocCommRing (selfAdjoint A) where
  __ := instNonAssocRing
  mul_comm := jordanMul_comm

/-- Real scalar multiplication commutes with Jordan multiplication. -/
scoped instance instSMulCommClass : SMulCommClass ℝ (selfAdjoint A) (selfAdjoint A) where
  smul_comm c a b := (jordanMul_smul_right a c b).symm

/-- Real scalar multiplication is a tower over Jordan multiplication. -/
scoped instance instIsScalarTower : IsScalarTower ℝ (selfAdjoint A) (selfAdjoint A) where
  smul_assoc c a b := jordanMul_smul_left c a b

/-- The Jordan product makes `selfAdjoint A` a commutative Jordan ring, in the sense of mathlib's
`IsCommJordan`: this is the connection from the abstract axioms in `Mathlib.Algebra.Jordan.Basic`
to the self-adjoint elements of an associative `StarRing`. -/
scoped instance instIsCommJordan : IsCommJordan (selfAdjoint A) where
  lmul_comm_rmul_rmul := jordanMul_jordanMul_jordanMul_self

end AlgebraStructure

end selfAdjoint

namespace ProbabilisticTheory

/-- The Jordan product of observables. -/
noncomputable abbrev Observable.jordanMul {A : Type*} [Ring A] [StarRing A] [Module ℝ A]
    [StarModule ℝ A] (a b : Observable A) :
    Observable A :=
  selfAdjoint.jordanMul a b

end ProbabilisticTheory
