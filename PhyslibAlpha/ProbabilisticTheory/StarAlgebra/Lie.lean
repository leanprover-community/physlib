/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Mathlib.Algebra.Lie.Basic
public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.Tactic.NoncommRing
public import PhyslibAlpha.ProbabilisticTheory.StarAlgebra.Jordan

/-!

# The Lie bracket of observables

The Lie bracket -(i / 2)(a b - b a) makes the observables a real Lie algebra.

## i. Overview

The commutator of two self-adjoint elements is skew-adjoint, so `⁅a, b⁆ = -(i / 2)(a b - b a)` is
self-adjoint. Together with the Jordan product it splits the product of observables, `a b = a ∘ b +
i ⁅a, b⁆`, and it makes the observables a real Lie algebra. The bracket is a scoped instance on
`selfAdjoint A`.

## ii. Key results

- `selfAdjoint.lieMul` : the Lie bracket `-(i / 2)(a b - b a)`.
- `selfAdjoint.isSelfAdjoint_mul_iff_commute` : `a b` is self-adjoint iff `a` and `b` commute.
- `selfAdjoint.mul_decomposition` : `a b = a ∘ b + i ⁅a, b⁆`.
- `selfAdjoint.leibniz_bracket` : the bracket satisfies the Leibniz rule.

## iii. Table of contents

- A. The Lie bracket
- B. Antisymmetry and additivity
- C. Lie ring
- D. Real Lie algebra
- E. Elementary identities

## iv. References

* None.

-/

@[expose] public section

namespace selfAdjoint
open ProbabilisticTheory

variable {A : Type*} [Ring A] [StarRing A] [Module ℂ A] [StarModule ℂ A]

/-! ## A. The Lie bracket -/

/-- The Lie bracket `-(i / 2)(a b - b a)` of two self-adjoint elements, again self-adjoint. -/
noncomputable def lieMul (a b : selfAdjoint A) : selfAdjoint A :=
  ⟨(-(Complex.I / 2)) • ((a : A) * b - (b : A) * a), by
    rw [mem_iff, star_smul, star_sub, star_mul, star_mul, a.property.star_eq, b.property.star_eq]
    have hI : star (-(Complex.I / 2) : ℂ) = Complex.I / 2 := by
      simp [Complex.ext_iff]
      norm_num
    rw [hI]
    module⟩

@[simp]
lemma val_lieMul (a b : selfAdjoint A) :
    ((lieMul a b : selfAdjoint A) : A) = (-(Complex.I / 2)) • ((a : A) * b - (b : A) * a) :=
  rfl

omit [Module ℂ A] [StarModule ℂ A] in
/-- The product of two self-adjoint elements is self-adjoint iff they commute. -/
lemma isSelfAdjoint_mul_iff_commute (a b : selfAdjoint A) :
    IsSelfAdjoint ((a : A) * (b : A)) ↔ Commute (a : A) (b : A) := by
  rw [isSelfAdjoint_iff, star_mul, a.property.star_eq, b.property.star_eq, commute_iff_eq, eq_comm]

/-- The ambient product of two self-adjoint elements splits into its normalized Jordan and Lie
parts: `a * b = (a ∘ b) + i ⁅a, b⁆`. -/
lemma mul_decomposition (a b : selfAdjoint A) :
    (a : A) * b =
      (jordanMul a b : A) + Complex.I • ((lieMul a b : selfAdjoint A) : A) := by
  rw [val_jordanMul, val_lieMul, smul_smul]
  have h2 : Complex.I * -(Complex.I / 2) = (2 : ℂ)⁻¹ := by
    rw [mul_neg, ← mul_div_assoc, Complex.I_mul_I]
    norm_num
  rw [h2]
  module

/-! ## B. Antisymmetry and additivity -/

/-- The Lie bracket is antisymmetric. -/
lemma lieMul_swap (a b : selfAdjoint A) : lieMul a b = -lieMul b a := by
  apply Subtype.ext
  simp only [val_lieMul, AddSubgroup.coe_neg]
  module

lemma lieMul_add_left (a b c : selfAdjoint A) :
    lieMul (a + b) c = lieMul a c + lieMul b c := by
  apply Subtype.ext
  simp only [val_lieMul, AddSubgroup.coe_add]
  rw [show ((a : A) + b) * c - (c : A) * ((a : A) + b) =
      ((a : A) * c - (c : A) * a) + ((b : A) * c - (c : A) * b) by noncomm_ring, smul_add]

lemma lieMul_add_right (a b c : selfAdjoint A) :
    lieMul a (b + c) = lieMul a b + lieMul a c := by
  apply Subtype.ext
  simp only [val_lieMul, AddSubgroup.coe_add]
  rw [show (a : A) * ((b : A) + c) - ((b : A) + c) * a =
      ((a : A) * b - (b : A) * a) + ((a : A) * c - (c : A) * a) by noncomm_ring, smul_add]

lemma lieMul_self (a : selfAdjoint A) : lieMul a a = 0 := by
  apply Subtype.ext
  simp [val_lieMul]

/-- The Lie bracket as a scoped bracket on `selfAdjoint A`. -/
noncomputable scoped instance instBracket : Bracket (selfAdjoint A) (selfAdjoint A) := ⟨lieMul⟩

@[simp]
lemma bracket_def (a b : selfAdjoint A) : ⁅a, b⁆ = lieMul a b := rfl

lemma coe_bracket (a b : selfAdjoint A) :
    ((⁅a, b⁆ : selfAdjoint A) : A) = (-(Complex.I / 2)) • ((a : A) * b - (b : A) * a) :=
  val_lieMul a b

/-! ## C. Lie ring -/

section LieRing

variable [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]

lemma leibniz_bracket (a b c : selfAdjoint A) :
    ⁅a, ⁅b, c⁆⁆ = ⁅⁅a, b⁆, c⁆ + ⁅b, ⁅a, c⁆⁆ := by
  apply Subtype.ext
  simp only [bracket_def, val_lieMul, AddSubgroup.coe_add]
  rw [mul_smul_comm, smul_mul_assoc, mul_smul_comm, smul_mul_assoc, mul_smul_comm, smul_mul_assoc,
    ← smul_sub, ← smul_sub, ← smul_sub, smul_smul, smul_smul, smul_smul, ← smul_add]
  congr 1
  noncomm_ring

/-- The self-adjoint elements form a Lie ring under the Lie bracket. -/
noncomputable scoped instance instLieRing : LieRing (selfAdjoint A) where
  add_lie := lieMul_add_left
  lie_add := lieMul_add_right
  lie_self := lieMul_self
  leibniz_lie := leibniz_bracket

/-! ## D. Real Lie algebra -/

lemma bracket_smul (t : ℝ) (a b : selfAdjoint A) :
    ⁅a, t • b⁆ = t • ⁅a, b⁆ := by
  apply Subtype.ext
  simp only [bracket_def, val_lieMul, selfAdjoint.val_smul, ← Complex.coe_smul]
  rw [mul_smul_comm, smul_mul_assoc]
  module

/-- The Lie bracket is compatible with the real scalar structure. -/
noncomputable scoped instance instLieAlgebra : LieAlgebra ℝ (selfAdjoint A) where
  toModule := inferInstance
  lie_smul := bracket_smul

end LieRing

/-! ## E. Elementary identities -/

lemma bracket_one_right (a : selfAdjoint A) : ⁅a, (1 : selfAdjoint A)⁆ = 0 := by
  apply Subtype.ext
  rw [coe_bracket]
  simp

lemma bracket_one_left (a : selfAdjoint A) : ⁅(1 : selfAdjoint A), a⁆ = 0 := by
  apply Subtype.ext
  rw [coe_bracket]
  simp

end selfAdjoint

namespace ProbabilisticTheory

/-- The Lie bracket of observables. -/
noncomputable abbrev Observable.lieMul {A : Type*} [Ring A] [StarRing A] [Module ℂ A]
    [StarModule ℂ A] (a b : Observable A) : Observable A :=
  selfAdjoint.lieMul a b

end ProbabilisticTheory
