/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ProbabilisticTheory.JordanOrderUnit.Observable
public import PhyslibAlpha.ProbabilisticTheory.OrderUnit.Normed
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Algebra.Ring.IsFormallyReal

/-!

# Normed Jordan algebras and JB-algebras

## i. Overview

`JBAlgebra` is a Banach Jordan algebra satisfying the JB axioms
(Hanche-Olsen–Størmer, *Jordan Operator Algebras*, Def. 3.1.1):

- `‖a ∘ b‖ ≤ ‖a‖ ‖b‖`;
- `‖a ∘ a‖ = ‖a‖ ^ 2`;
- `‖a ∘ a‖ ≤ ‖a ∘ a + b ∘ b‖`.

It carries no order. `IsJBOrderUnit` is the ordered version: an order-unit space whose order-unit
norm is the given norm.

`NormedJordanAlgebra` bundles the ring, module and metric structure of a normed Jordan algebra
in one class, and `JBAlgebra` adds completeness and the JB axioms.

## ii. Key definitions and results

- `NormedJordanAlgebra E` : a real normed unital Jordan algebra.
- `JBAlgebra E` : a JB-algebra.
- `JBAlgebra.norm_mul_self_le_norm_mul_self_add_mul_self` : monotonicity of the norm on sums of
  squares.

## iii. Table of contents

- A. Normed Jordan algebras
- B. JB-algebras
- C. Basic consequences

-/

@[expose] public section

namespace ProbabilisticTheory

/-! ## A. Normed Jordan algebras -/

/-- A real normed unital Jordan algebra. -/
class NormedJordanAlgebra (E : Type*) extends Norm E, MetricSpace E, NonAssocCommRing E,
    Module ℝ E where
  /-- The metric is induced by the additive norm. -/
  dist_eq : ∀ x y : E, dist x y = ‖-x + y‖
  /-- Real scalar multiplication is norm-bounded. -/
  norm_smul_le : ∀ (r : ℝ) (x : E), ‖r • x‖ ≤ ‖r‖ * ‖x‖
  /-- Real scalars commute with right Jordan multiplication. -/
  smul_comm : ∀ (r : ℝ) (x y : E), r • (x * y) = x * (r • y)
  /-- Real scalar multiplication is a tower over Jordan multiplication. -/
  smul_assoc : ∀ (r : ℝ) (x y : E), (r • x) * y = r • (x * y)
  /-- The commutative Jordan identity. -/
  jordan_identity : ∀ x y : E, x * y * (x * x) = x * (y * (x * x))
  /-- The Jordan product is norm-submultiplicative. -/
  norm_mul_le : ∀ x y : E, ‖x * y‖ ≤ ‖x‖ * ‖y‖

attribute [instance 10] NormedJordanAlgebra.toNonAssocCommRing

/-- The coherent additive metric structure underlying a normed Jordan algebra. -/
instance {E : Type*} [s : NormedJordanAlgebra E] : NormedAddCommGroup E := { s with }

/-- The coherent real normed-space structure underlying a normed Jordan algebra. -/
instance {E : Type*} [s : NormedJordanAlgebra E] : NormedSpace ℝ E :=
  { s.toModule with norm_smul_le := s.norm_smul_le }

/-- Scalar actions commute with Jordan multiplication. -/
instance {E : Type*} [s : NormedJordanAlgebra E] : SMulCommClass ℝ E E := ⟨s.smul_comm⟩

/-- Scalar actions form a tower over Jordan multiplication. -/
instance {E : Type*} [s : NormedJordanAlgebra E] : IsScalarTower ℝ E E := ⟨s.smul_assoc⟩

/-- A normed Jordan algebra satisfies Mathlib's commutative Jordan predicate. -/
instance {E : Type*} [s : NormedJordanAlgebra E] : IsCommJordan E := ⟨s.jordan_identity⟩

/-! ## B. JB-algebras -/

/-- A JB-algebra: a complete real normed Jordan algebra whose norm realizes squares exactly and is
monotone under addition of squares. No order is chosen at this analytic level. -/
class JBAlgebra (E : Type*) [NormedJordanAlgebra E] : Prop extends CompleteSpace E where
  /-- Squares realize the norm exactly: the JB (Jordan–Banach) axiom. -/
  norm_mul_self : ∀ a : E, ‖a * a‖ = ‖a‖ ^ 2
  /-- Order-norm compatibility: a square's norm cannot exceed the norm of its sum with another
  square. -/
  norm_mul_self_le_add : ∀ a b : E, ‖a * a‖ ≤ ‖a * a + b * b‖

/-- A coherent ordered realization of a JB-algebra. It bundles the analytic Jordan algebra,
order-unit structure, positive-square compatibility, and completeness without instance diamonds. -/
class IsJBOrderUnit (E : Type*) extends NormedJordanAlgebra E, IsJordanOrderUnit E,
    ArchimedeanOrderUnitSpace E, JBAlgebra E where
  norm_eq_orderUnitNorm : ∀ x : E, ‖x‖ = ArchimedeanOrderUnitSpace.orderUnitNorm x

namespace JBAlgebra

section Analytic

variable {E : Type*} [NormedJordanAlgebra E] [JBAlgebra E]

/-! ## C. Basic consequences -/

/-- `‖a ∘ a‖ ≤ ‖a ∘ a + b ∘ b‖`. -/
lemma norm_mul_self_le_norm_mul_self_add_mul_self (a b : E) : ‖a * a‖ ≤ ‖a * a + b * b‖ :=
  norm_mul_self_le_add a b

/-- The Jordan square of a norm-`1` element has norm `1`. -/
lemma norm_mul_self_of_norm_eq_one {a : E} (ha : ‖a‖ = 1) : ‖a * a‖ = 1 := by
  rw [norm_mul_self, ha, one_pow]

/-- A Jordan square in a JB-algebra is zero only when its root is zero. -/
lemma eq_zero_of_mul_self_eq_zero {a : E} (ha : a * a = 0) : a = 0 := by
  apply norm_eq_zero.mp
  apply sq_eq_zero_iff.mp
  rw [← norm_mul_self a, ha, norm_zero]

/-- The zero-square criterion as an equivalence, convenient when transporting formal reality to
subalgebras and quotients. -/
lemma mul_self_eq_zero_iff {a : E} : a * a = 0 ↔ a = 0 :=
  ⟨eq_zero_of_mul_self_eq_zero, fun h => by simp [h]⟩

end Analytic

section Ordered

variable {E : Type*} [IsJBOrderUnit E]

/-- In an ordered JB realization, the analytic norm is exactly the order-unit norm. -/
lemma norm_eq_orderUnitNorm (x : E) : ‖x‖ = ArchimedeanOrderUnitSpace.orderUnitNorm x :=
  IsJBOrderUnit.norm_eq_orderUnitNorm x

/-- The identity map from the order-unit-norm copy to a JB algebra is an isometry. -/
noncomputable def withOrderUnitNormIsometryEquiv : WithOrderUnitNorm E ≃ₗᵢ[ℝ] E where
  __ := (WithOrderUnitNorm.linearEquiv (E := E)).symm
  norm_map' x := (norm_eq_orderUnitNorm (show E from x)).trans rfl

/-- A JB algebra is complete in its order-unit norm, since that norm is its JB norm. -/
instance : CompleteSpace (WithOrderUnitNorm E) :=
  (completeSpace_congr (e := withOrderUnitNormIsometryEquiv.toLinearEquiv.toEquiv)
    withOrderUnitNormIsometryEquiv.isometry.isUniformEmbedding).mpr inferInstance

/-- A nonnegative scalar bounds the analytic JB norm exactly when its order-unit multiple bounds
the observable on both sides. This is the public norm/order interface for an ordered JB algebra. -/
lemma norm_le_iff_order_bounds {x : E} {r : ℝ} (hr : 0 ≤ r) :
    ‖x‖ ≤ r ↔ -(r • (1 : E)) ≤ x ∧ x ≤ r • (1 : E) := by
  constructor
  · intro h
    rw [norm_eq_orderUnitNorm] at h
    exact (ArchimedeanOrderUnitSpace.mem_orderUnitBounds_iff.mpr h).2
  · rintro ⟨hlow, hupp⟩
    rw [norm_eq_orderUnitNorm]
    exact ArchimedeanOrderUnitSpace.mem_orderUnitBounds_iff.mp ⟨hr, hlow, hupp⟩

/-- The unit interval is contained in the analytic closed unit ball of an ordered JB algebra. -/
lemma norm_le_one_of_zero_le_of_le_one {x : E} (hx : 0 ≤ x) (hxu : x ≤ 1) : ‖x‖ ≤ 1 := by
  apply (norm_le_iff_order_bounds (x := x) (r := 1) zero_le_one).mpr
  constructor
  · calc
      -((1 : ℝ) • (1 : E)) ≤ 0 := by simp [OrderUnitSpace.one_nonneg]
      _ ≤ x := hx
  · simpa using hxu

/-- The positive cone is closed for the supplied JB norm.  This transports the order-unit
closedness argument to the analytic norm through `norm_eq_orderUnitNorm`, and is the limit step
needed by intrinsic square-root approximations. -/
lemma isClosed_nonneg : IsClosed {x : E | 0 ≤ x} := by
  apply IsSeqClosed.isClosed
  intro x p hx hp
  apply neg_nonpos.mp
  apply ArchimedeanOrderUnitSpace.le_zero_of_forall_pos_smul_one_le
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hp ε hε
  have hdist := hN N le_rfl
  have hnorm : ArchimedeanOrderUnitSpace.orderUnitNorm (p - x N) < ε := by
    rw [dist_eq_norm] at hdist
    change ‖x N - p‖ < ε at hdist
    calc
      ArchimedeanOrderUnitSpace.orderUnitNorm (p - x N) = ‖p - x N‖ :=
        (norm_eq_orderUnitNorm (p - x N)).symm
      _ = ‖x N - p‖ := by rw [← norm_neg, neg_sub]
      _ < ε := hdist
  have hdiff : -(ε • (1 : E)) ≤ p - x N := by
    have hmono : ArchimedeanOrderUnitSpace.orderUnitNorm (p - x N) • (1 : E) ≤ ε • (1 : E) := by
      calc
        ArchimedeanOrderUnitSpace.orderUnitNorm (p - x N) • (1 : E) =
            ε • (1 : E) - (ε - ArchimedeanOrderUnitSpace.orderUnitNorm (p - x N)) • (1 : E) := by
          rw [← sub_smul, sub_sub_cancel]
        _ ≤ ε • (1 : E) := sub_le_self _
          (smul_nonneg (sub_nonneg.mpr hnorm.le) OrderUnitSpace.one_nonneg)
    exact (neg_le_neg hmono).trans
      (ArchimedeanOrderUnitSpace.neg_orderUnitNorm_smul_one_le (p - x N))
  have hnegp : -p ≤ ε • (1 : E) - x N := by
    have hshift := add_le_add_right (neg_le_neg hdiff) (-x N)
    convert hshift using 1 <;> abel
  calc
    -p ≤ ε • (1 : E) - x N := hnegp
    _ ≤ ε • (1 : E) := sub_le_self _ (hx N)

/-- Every finite sum of Jordan squares is positive. -/
lemma isSumSq_nonneg {s : E} (hs : IsSumSq s) : 0 ≤ s := by
  induction hs with
  | zero => exact le_rfl
  | sq_add a _ ih => exact add_nonneg (IsJordanOrderUnit.mul_self_nonneg a) ih

/-- A JB-algebra has no square root of `-1`.  This elementary ordered consequence is the
key algebraic obstruction separating the real JB one-generator algebra from arbitrary real
uniform Banach algebras (where the real spectrum may be empty). -/
lemma no_mul_self_eq_neg_one [Nontrivial E] (a : E) : a * a ≠ -1 := by
  intro h
  have hnonneg : (0 : E) ≤ a * a := IsJordanOrderUnit.mul_self_nonneg a
  have hone : (0 : E) < (1 : E) :=
    lt_of_le_of_ne OrderUnitSpace.one_nonneg (Ne.symm one_ne_zero)
  have hneg : (-1 : E) < 0 := neg_lt_zero.mpr hone
  exact (not_le_of_gt hneg) (h ▸ hnonneg)

/-- A sum of two Jordan squares can vanish only when both roots vanish.  This is the
two-square form of formal reality and is useful when analysing quadratic real factors in the
one-generator resolvent. -/
lemma add_mul_self_eq_zero_iff {a b : E} :
    a * a + b * b = 0 ↔ a = 0 ∧ b = 0 := by
  constructor
  · intro h
    have hsq := (add_eq_zero_iff_of_nonneg (IsJordanOrderUnit.mul_self_nonneg a)
      (IsJordanOrderUnit.mul_self_nonneg b)).mp h
    exact ⟨eq_zero_of_mul_self_eq_zero hsq.1, eq_zero_of_mul_self_eq_zero hsq.2⟩
  · rintro ⟨rfl, rfl⟩
    simp

/-- The positive quadratic factor `a² + 1` cannot vanish in a nontrivial JB-algebra. -/
lemma mul_self_add_one_ne_zero [Nontrivial E] (a : E) : a * a + 1 ≠ 0 := by
  intro h
  have h' : a * a + (1 : E) * 1 = 0 := by simpa using h
  exact one_ne_zero ((add_mul_self_eq_zero_iff.mp h').2)

/-- A JB-algebra is formally real: a sum of squares vanishes only if every term does. -/
noncomputable instance instIsFormallyReal : IsFormallyReal E :=
  IsFormallyReal.of_eq_zero_of_mul_self_of_eq_zero_of_add
    (fun {a} ha => eq_zero_of_mul_self_eq_zero ha)
    (by
      intro s₁ s₂ hs₁ hs₂ hsum
      exact (add_eq_zero_iff_of_nonneg (isSumSq_nonneg hs₁) (isSumSq_nonneg hs₂)).mp hsum |>.1)

/-- In an ordered JB-algebra the norm is the order-unit norm, as a linear isometric equivalence. -/
noncomputable def toWithOrderUnitNormLinearIsometryEquiv :
    E ≃ₗᵢ[ℝ] WithOrderUnitNorm E where
  __ := WithOrderUnitNorm.linearEquiv
  norm_map' x := by
    change ArchimedeanOrderUnitSpace.orderUnitNorm x = ‖x‖
    exact (norm_eq_orderUnitNorm x).symm

/-- An ordered JB-algebra is complete for its order-unit norm. -/
lemma completeWithOrderUnitNorm : CompleteSpace (WithOrderUnitNorm E) := by
  exact (completeSpace_congr
    (e := (toWithOrderUnitNormLinearIsometryEquiv (E := E)).symm.toLinearEquiv.toEquiv)
    (toWithOrderUnitNormLinearIsometryEquiv (E := E)).symm.isometry.isUniformEmbedding).mpr
      JBAlgebra.toCompleteSpace

end Ordered

end JBAlgebra

end ProbabilisticTheory
