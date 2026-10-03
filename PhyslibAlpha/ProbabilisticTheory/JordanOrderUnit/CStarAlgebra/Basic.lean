/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ProbabilisticTheory.JordanOrderUnit.JB.Basic
public import PhyslibAlpha.ProbabilisticTheory.StarAlgebra.Jordan
public import PhyslibAlpha.ProbabilisticTheory.CStarAlgebra.OrderUnit

/-!

# The self-adjoint part of a C⋆-algebra is a JB-algebra

The self-adjoint elements of a unital C⋆-algebra form a JB-algebra under `½ (a b + b a)`.

## i. Overview

The self-adjoint elements of a unital C⋆-algebra, with the Jordan product `a ∘ b = ½ (a b + b a)`,
form a JB-algebra. With this normalization the Jordan square is the ordinary square and the
quadratic representation is `U_a b = a b a`, and Jordan projections are the ordinary projections.
The instances are scoped to `JB`.

## ii. Key results

- `JB.instIsJordanOrderUnit`, `JB.instJBAlgebra` : the Jordan order-unit and JB-algebra structures.
- `JB.mul_self_eq` : the Jordan square is the ordinary square.
- `JB.quadRep_eq_conj` : `U_a b = a b a`.
- `JB.isJordanProjection_iff_isIdempotentElem` : Jordan projections are the ordinary projections.
- `JB.jordanOrthogonal_iff` : Jordan orthogonality of `p`, `q` is `p q + q p = 0`.

## iii. Table of contents

- A. C⋆ order compatibility
- B. The JB-algebra instance
- C. Squares, `U_a = aba` and projections

## iv. References

* None.

-/

@[expose] public section

namespace ProbabilisticTheory

namespace JB

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

open scoped selfAdjoint

/-! ## A. C⋆ order compatibility -/

omit [PartialOrder A] [StarOrderedRing A] in
lemma one_mul (a : selfAdjoint A) : (1 : selfAdjoint A) * a = a := by
  apply Subtype.ext
  rw [selfAdjoint.mul_def, selfAdjoint.val_jordanMul]
  show (2 : ℝ)⁻¹ • ((1 : A) * (a : A) + (a : A) * (1 : A)) = (a : A)
  rw [_root_.one_mul, _root_.mul_one, ← two_smul ℝ (a : A), smul_smul,
    inv_mul_cancel₀ (two_ne_zero), one_smul]

omit [PartialOrder A] [StarOrderedRing A] in
/-- The Jordan square of a self-adjoint element, for the normalized product, is exactly its
ordinary (associative) square. This is the reason `moment`/`variance` computed via the abstract
`IsJordanOrderUnit` layer agree with the operator-theoretic ones. -/
lemma mul_self_eq (a : selfAdjoint A) : ((a * a : selfAdjoint A) : A) = (a : A) * (a : A) := by
  rw [selfAdjoint.mul_def, selfAdjoint.val_jordanMul, ← two_smul ℝ ((a:A)*(a:A)), smul_smul,
    inv_mul_cancel₀ (two_ne_zero), one_smul]

lemma mul_self_nonneg (a : selfAdjoint A) : 0 ≤ a * a := by
  show (0 : A) ≤ ((a * a : selfAdjoint A) : A)
  rw [mul_self_eq]
  calc (0 : A) ≤ star (a : A) * (a : A) := star_mul_self_nonneg _
    _ = (a : A) * (a : A) := by rw [a.2]

/-- The self-adjoint part of a C⋆-algebra is a Jordan order-unit space. -/
noncomputable scoped instance instIsJordanOrderUnit : IsJordanOrderUnit (selfAdjoint A) :=
  { (inferInstance : NonAssocCommRing (selfAdjoint A)),
    (inferInstance : OrderUnitSpace (selfAdjoint A)),
    (inferInstance : SMulCommClass ℝ (selfAdjoint A) (selfAdjoint A)),
    (inferInstance : IsScalarTower ℝ (selfAdjoint A) (selfAdjoint A)),
    (inferInstance : IsCommJordan (selfAdjoint A)) with
  mul_self_nonneg := mul_self_nonneg
  one_sub_mul_one_sub a := by
    rw [sub_mul, mul_sub, mul_sub, _root_.one_mul, _root_.one_mul, _root_.mul_one]
    abel
  mul_one_sub a := by
    rw [mul_sub, _root_.mul_one] }

/-! ## B. The JB-algebra instance -/

omit [PartialOrder A] [StarOrderedRing A] in
lemma norm_mul_le' (a b : selfAdjoint A) : ‖a * b‖ ≤ ‖a‖ * ‖b‖ := by
  show ‖((a * b : selfAdjoint A) : A)‖ ≤ ‖(a : A)‖ * ‖(b : A)‖
  rw [selfAdjoint.mul_def, selfAdjoint.val_jordanMul, norm_smul]
  calc ‖(2 : ℝ)⁻¹‖ * ‖(a : A) * (b : A) + (b : A) * (a : A)‖
      ≤ ‖(2 : ℝ)⁻¹‖ * (‖(a : A) * (b : A)‖ + ‖(b : A) * (a : A)‖) := by
        gcongr; exact norm_add_le _ _
    _ ≤ ‖(2 : ℝ)⁻¹‖ * (‖(a : A)‖ * ‖(b : A)‖ + ‖(b : A)‖ * ‖(a : A)‖) := by
        gcongr <;> exact _root_.norm_mul_le _ _
    _ = ‖(a : A)‖ * ‖(b : A)‖ := by
        rw [Real.norm_eq_abs, abs_of_pos (by norm_num : (0:ℝ) < 2⁻¹)]; ring

/-- The self-adjoint part carries one coherent normed Jordan structure inherited from the ambient
Cstar algebra. -/
noncomputable scoped instance instNormedJordanAlgebra : NormedJordanAlgebra (selfAdjoint A) where
  __ := selfAdjoint.instNonAssocCommRing
  __ := (inferInstance : Norm (selfAdjoint A))
  __ := (inferInstance : MetricSpace (selfAdjoint A))
  __ := (inferInstance : Module ℝ (selfAdjoint A))
  dist_eq := NormedAddCommGroup.dist_eq
  norm_smul_le := NormedSpace.norm_smul_le
  smul_comm := fun c a b => (selfAdjoint.jordanMul_smul_right a c b).symm
  smul_assoc := selfAdjoint.jordanMul_smul_left
  jordan_identity := selfAdjoint.jordanMul_jordanMul_jordanMul_self
  norm_mul_le := norm_mul_le'

/-- The self-adjoint part of a Cstar algebra is complete because it is the closed fixed-point set
of the continuous star operation. -/
scoped instance instCompleteSpace : CompleteSpace (selfAdjoint A) :=
  (isClosed_eq continuous_star continuous_id).completeSpace_coe

lemma norm_mul_self' (a : selfAdjoint A) : ‖a * a‖ = ‖a‖ ^ 2 := by
  show ‖((a * a : selfAdjoint A) : A)‖ = ‖(a : A)‖ ^ 2
  rw [mul_self_eq]
  exact IsSelfAdjoint.norm_mul_self a.2

lemma norm_mul_self_le_add' (a b : selfAdjoint A) : ‖a * a‖ ≤ ‖a * a + b * b‖ := by
  show ‖((a * a : selfAdjoint A) : A)‖ ≤ ‖((a * a + b * b : selfAdjoint A) : A)‖
  rw [mul_self_eq]
  have hab : ((a * a + b * b : selfAdjoint A) : A) = (a : A) * (a : A) + (b : A) * (b : A) := by
    rw [AddSubgroup.coe_add, mul_self_eq, mul_self_eq]
  rw [hab]
  have h0 : (0 : A) ≤ (b : A) * (b : A) := by
    calc (0 : A) ≤ star (b : A) * (b : A) := star_mul_self_nonneg _
      _ = (b : A) * (b : A) := by rw [b.2]
  have h0' : (0 : A) ≤ (a : A) * (a : A) := by
    calc (0 : A) ≤ star (a : A) * (a : A) := star_mul_self_nonneg _
      _ = (a : A) * (a : A) := by rw [a.2]
  exact CStarAlgebra.norm_le_norm_of_le_of_nonneg (le_add_of_nonneg_right h0) h0'

/-- The self-adjoint part of a unital C⋆-algebra is a JB-algebra under `a ∘ b = ½ (a b + b a)`. -/
scoped instance instJBAlgebra : JBAlgebra (selfAdjoint A) where
  __ := instCompleteSpace
  norm_mul_self := norm_mul_self'
  norm_mul_self_le_add := norm_mul_self_le_add'

/-! ## C. Squares, `U_a = aba` and projections -/

open scoped JordanAlgebra

/-- **`U_a b = a b a`** for self-adjoint elements of a C⋆-algebra. -/
lemma quadRep_eq_conj (a b : selfAdjoint A) :
    ((JordanAlgebra.quadRep a b : selfAdjoint A) : A) = (a : A) * (b : A) * (a : A) := by
  have key : (a:A)*((a:A)*(b:A)+(b:A)*(a:A)) + ((a:A)*(b:A)+(b:A)*(a:A))*(a:A)
      - ((a:A)*(a:A)*(b:A) + (b:A)*((a:A)*(a:A))) = (2:A) * ((a:A)*(b:A)*(a:A)) := by
    noncomm_ring
  have hc : (2:ℝ) * (2:ℝ)⁻¹ * (2:ℝ)⁻¹ = (2:ℝ)⁻¹ := by norm_num
  have hsum : (2:ℝ)⁻¹ + (2:ℝ)⁻¹ = 1 := by norm_num
  have hsq : (2 : ℝ)⁻¹ • ((a : A) * (a : A) + (a : A) * (a : A)) =
      (a : A) * (a : A) := by
    rw [← two_smul ℝ ((a : A) * (a : A)), smul_smul,
      inv_mul_cancel₀ (two_ne_zero), one_smul]
  rw [JordanAlgebra.quadRep_apply, AddSubgroup.coe_sub, selfAdjoint.val_smul,
    JordanAlgebra.jpow_two]
  simp only [selfAdjoint.coe_mul]
  rw [hsq, mul_smul_comm, smul_mul_assoc, ← smul_add, smul_smul, smul_smul, hc, ← smul_sub,
    key, two_mul, smul_add, ← add_smul, hsum, one_smul]

omit [PartialOrder A] [StarOrderedRing A] in
/-- **Realization identity**: a Jordan projection for the normalized product is exactly an ordinary
idempotent, `p² = p`. -/
lemma isJordanProjection_iff_isIdempotentElem {p : selfAdjoint A} :
    JordanAlgebra.IsJordanProjection p ↔ IsIdempotentElem (p : A) := by
  unfold JordanAlgebra.IsJordanProjection IsIdempotentElem
  rw [← mul_self_eq, Subtype.ext_iff]

omit [PartialOrder A] [StarOrderedRing A] in
/-- **Realization identity**: Jordan orthogonality for the normalized product is exactly ordinary
operator orthogonality `p q = 0`. -/
lemma jordanOrthogonal_iff {p q : selfAdjoint A} :
    JordanAlgebra.JordanOrthogonal p q ↔ (p : A) * (q : A) + (q : A) * (p : A) = 0 := by
  unfold JordanAlgebra.JordanOrthogonal
  rw [Subtype.ext_iff, selfAdjoint.mul_def, selfAdjoint.val_jordanMul, AddSubgroup.coe_zero,
    smul_eq_zero]
  simp [(by norm_num : (2:ℝ)⁻¹ ≠ 0)]

end JB

end ProbabilisticTheory
