/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.AlgebraicFramework.JordanOrderUnit.Quadratic.Fundamental
public import PhyslibAlpha.AlgebraicFramework.Algebra.Derivation
public import Mathlib.Algebra.Lie.Basic

/-!
# Jordan derivations and infinitesimal symmetries

This is the bundled companion to the generic predicate `IsDerivation`.  A Jordan derivation is
an infinitesimal reversible symmetry of an observable algebra; the module gives such generators
a stable carrier, while `inner` packages commutators of multiplication operators.  It is wholly
algebraic and sits below order units, JB norms, Cstar realizations, and JBW normality.

The design is adapted from Cobord's `Jordan/StructureAlgebra.lean`, but reuses PhyslibAlpha's
canonical `IsDerivation`, `innerDerivation`, and proved triple-commutator identities rather than
introducing a parallel Jordan class or multiplication-operator API.
-/

@[expose] public section

namespace JordanAlgebra

variable {E : Type*} [NonAssocCommRing E] [Module ℝ E] [SMulCommClass ℝ E E]
  [IsScalarTower ℝ E E]

/-- A bundled real Jordan derivation. -/
structure JordanDerivation (E : Type*) [NonAssocCommRing E] [Module ℝ E] where
  /-- The underlying real-linear infinitesimal generator. -/
  toLinearMap : E →ₗ[ℝ] E
  leibniz' : IsDerivation toLinearMap

namespace JordanDerivation

variable {D D₁ D₂ : JordanDerivation E}

instance : CoeFun (JordanDerivation E) (fun _ => E → E) := ⟨fun D => D.toLinearMap⟩
instance : Coe (JordanDerivation E) (E →ₗ[ℝ] E) := ⟨fun D => D.toLinearMap⟩

omit [SMulCommClass ℝ E E] [IsScalarTower ℝ E E] in
@[ext] theorem ext (h : ∀ x, D₁ x = D₂ x) : D₁ = D₂ := by
  cases D₁
  cases D₂
  simp only at h
  congr
  ext x
  exact h x

omit [SMulCommClass ℝ E E] [IsScalarTower ℝ E E] in
@[simp] theorem leibniz (D : JordanDerivation E) (x y : E) :
    D (x * y) = D x * y + x * D y := D.leibniz' x y

/-- All derivations as a submodule of linear endomorphisms. -/
def submodule : Submodule ℝ (E →ₗ[ℝ] E) where
  carrier := {D | IsDerivation D}
  zero_mem' := IsDerivation.zero
  add_mem' hD hE := IsDerivation.add hD hE
  smul_mem' c _ hD := IsDerivation.smul c hD

/-- The zero infinitesimal symmetry. -/
instance : Zero (JordanDerivation E) := ⟨⟨0, IsDerivation.zero⟩⟩

/-- Addition of infinitesimal symmetries. -/
instance : Add (JordanDerivation E) :=
  ⟨fun D₁ D₂ => ⟨D₁.toLinearMap + D₂.toLinearMap, IsDerivation.add D₁.leibniz' D₂.leibniz'⟩⟩

/-- Negation of infinitesimal symmetries. -/
instance : Neg (JordanDerivation E) :=
  ⟨fun D => ⟨-D.toLinearMap, IsDerivation.neg D.leibniz'⟩⟩

omit [SMulCommClass ℝ E E] [IsScalarTower ℝ E E] in
@[simp] theorem zero_apply (x : E) : (0 : JordanDerivation E) x = 0 := rfl

omit [SMulCommClass ℝ E E] [IsScalarTower ℝ E E] in
@[simp] theorem add_apply (D₁ D₂ : JordanDerivation E) (x : E) : (D₁ + D₂) x = D₁ x + D₂ x := rfl

omit [SMulCommClass ℝ E E] [IsScalarTower ℝ E E] in
@[simp] theorem neg_apply (D : JordanDerivation E) (x : E) : (-D) x = -D x := rfl

/-- Scalar multiples of infinitesimal symmetries. -/
instance : SMul ℝ (JordanDerivation E) :=
  ⟨fun c D => ⟨c • D.toLinearMap, IsDerivation.smul c D.leibniz'⟩⟩

@[simp] theorem smul_apply (c : ℝ) (D : JordanDerivation E) (x : E) : (c • D) x = c • D x := rfl

omit [SMulCommClass ℝ E E] [IsScalarTower ℝ E E] in
/-- Every infinitesimal symmetry fixes the unit to first order. -/
theorem map_one_eq_zero (D : JordanDerivation E) : D 1 = 0 := by
  have h : D 1 = D 1 + D 1 := by simpa using D.leibniz 1 1
  apply add_right_cancel (b := D 1)
  simpa using h.symm

/-- Jordan derivations form an additive commutative group. -/
instance : AddCommGroup (JordanDerivation E) where
  add_assoc D₁ D₂ D₃ := by ext x; simp only [add_apply]; abel
  zero_add D := by ext x; simp
  add_zero D := by ext x; simp
  add_comm D₁ D₂ := by ext x; simp only [add_apply]; abel
  neg_add_cancel D := by ext x; simp
  sub_eq_add_neg D₁ D₂ := by ext x; rfl
  nsmul := nsmulRec
  zsmul := zsmulRec

/-- Jordan derivations form a real vector space. -/
instance : Module ℝ (JordanDerivation E) where
  one_smul D := by ext x; simp
  mul_smul c d D := by
    ext x
    change (c * d) • D.toLinearMap x = c • d • D.toLinearMap x
    exact mul_smul c d (D.toLinearMap x)
  smul_zero c := by ext x; simp only [smul_apply, zero_apply, smul_zero]
  smul_add c D₁ D₂ := by
    ext x
    change c • (D₁.toLinearMap x + D₂.toLinearMap x) =
      c • D₁.toLinearMap x + c • D₂.toLinearMap x
    exact smul_add c (D₁.toLinearMap x) (D₂.toLinearMap x)
  add_smul c d D := by
    ext x
    change (c + d) • D.toLinearMap x = c • D.toLinearMap x + d • D.toLinearMap x
    exact add_smul c d (D.toLinearMap x)
  zero_smul D := by ext x; simp only [smul_apply, zero_smul, zero_apply]

/-- The commutator of two derivations is again a derivation. -/
def comm (D₁ D₂ : JordanDerivation E) : JordanDerivation E where
  toLinearMap := D₁.toLinearMap.comp D₂.toLinearMap - D₂.toLinearMap.comp D₁.toLinearMap
  leibniz' := by
    intro x y
    simp only [LinearMap.sub_apply, LinearMap.comp_apply]
    rw [D₂.leibniz x y, D₁.leibniz x y]
    simp only [map_add]
    rw [D₁.leibniz, D₁.leibniz, D₂.leibniz, D₂.leibniz]
    simp only [sub_mul, mul_sub]
    module

omit [SMulCommClass ℝ E E] [IsScalarTower ℝ E E] in
@[simp] theorem comm_apply (D₁ D₂ : JordanDerivation E) (x : E) :
    comm D₁ D₂ x = D₁ (D₂ x) - D₂ (D₁ x) := rfl

/-- Derivations carry their canonical commutator bracket. -/
instance : Bracket (JordanDerivation E) (JordanDerivation E) := ⟨comm⟩

omit [SMulCommClass ℝ E E] [IsScalarTower ℝ E E] in
@[simp] theorem lie_apply (D₁ D₂ : JordanDerivation E) (x : E) :
    ⁅D₁, D₂⁆ x = D₁ (D₂ x) - D₂ (D₁ x) := rfl

/-- Infinitesimal Jordan symmetries form a Lie ring under commutator. -/
instance : LieRing (JordanDerivation E) where
  add_lie D₁ D₂ D₃ := by
    ext x
    simp only [lie_apply, add_apply, map_add]
    abel
  lie_add D₁ D₂ D₃ := by
    ext x
    simp only [lie_apply, add_apply, map_add]
    abel
  lie_self D := by
    ext x
    simp only [lie_apply, zero_apply]
    abel
  leibniz_lie D₁ D₂ D₃ := by
    ext x
    simp only [lie_apply, add_apply, map_sub]
    abel

/-- The commutator Lie ring of derivations is a real Lie algebra. -/
instance : LieAlgebra ℝ (JordanDerivation E) where
  lie_smul c D₁ D₂ := by
    ext x
    simp only [lie_apply, smul_apply, map_smul, smul_sub]

end JordanDerivation

section Inner

variable [IsCommJordan E]

/-- The canonical inner Jordan derivation, generated by two observables. -/
def inner (a b : E) : JordanDerivation E where
  toLinearMap := innerDerivation a b
  leibniz' := fun x y => innerDerivation_mul a b x y

omit [IsScalarTower ℝ E E] in
@[simp] theorem inner_apply (a b x : E) : inner a b x = a * (b * x) - b * (a * x) := rfl

omit [IsScalarTower ℝ E E] in
/-- The inner-derivation commutator law in bundled infinitesimal-symmetry form. -/
theorem inner_comm (a b c d : E) :
    JordanDerivation.comm (inner a b) (inner c d) =
      inner (inner a b c) d + inner c (inner a b d) := by
  ext x
  change (innerDerivation a b).comp (innerDerivation c d) x -
      (innerDerivation c d).comp (innerDerivation a b) x =
    (innerDerivation (innerDerivation a b c) d + innerDerivation c (innerDerivation a b d)) x
  exact DFunLike.congr_fun (innerDerivation_comm a b c d) x

end Inner

end JordanAlgebra
