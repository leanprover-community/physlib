/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.AlgebraicFramework.JordanOrderUnit.Operator
public import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-!
# Spin-factor Jordan algebras

A spin factor is the Jordan algebra carried by `V × R` with product

`(x, a) ∘ (y, b) = (a • y + b • x, B x y + a * b)`.

This is the basic non-associative finite-dimensional observable model: over `ℝ`, a positive
definite form later supplies the Lorentz cone and its JB norm.  The present file intentionally
stops at the algebraic layer.  Positivity, completeness, and order-unit compatibility are
additional analytic data and must not be manufactured by this instance.

The construction is adapted from Cobord's `Jordan/SpinFactor.lean`, but uses PhyslibAlpha's
canonical `NonAssocCommRing`/`IsCommJordan` interface rather than importing a parallel class.
-/

@[expose] public section

namespace JordanAlgebra

variable (R V : Type*) [CommRing R] [AddCommGroup V] [Module R V]

/-- The spin factor determined by a bilinear form.  The synonym keeps products belonging to
different forms from becoming definitionally interchangeable. -/
abbrev SpinFactor (_B : LinearMap.BilinForm R V) : Type _ := V × R

namespace SpinFactor

variable {R V}
variable (B : LinearMap.BilinForm R V)

instance : AddCommGroup (SpinFactor R V B) := inferInstanceAs (AddCommGroup (V × R))
instance : Module R (SpinFactor R V B) := inferInstanceAs (Module R (V × R))

@[ext] theorem ext {z w : SpinFactor R V B} (hV : z.1 = w.1) (hR : z.2 = w.2) : z = w :=
  Prod.ext hV hR

@[simp] theorem add_fst (z w : SpinFactor R V B) : (z + w).1 = z.1 + w.1 := rfl
@[simp] theorem add_snd (z w : SpinFactor R V B) : (z + w).2 = z.2 + w.2 := rfl
@[simp] theorem zero_fst : (0 : SpinFactor R V B).1 = 0 := rfl
@[simp] theorem zero_snd : (0 : SpinFactor R V B).2 = 0 := rfl
@[simp] theorem neg_fst (z : SpinFactor R V B) : (-z).1 = -z.1 := rfl
@[simp] theorem neg_snd (z : SpinFactor R V B) : (-z).2 = -z.2 := rfl
@[simp] theorem smul_fst (r : R) (z : SpinFactor R V B) : (r • z).1 = r • z.1 := rfl
@[simp] theorem smul_snd (r : R) (z : SpinFactor R V B) : (r • z).2 = r • z.2 := rfl

/-- Constructor exposing the vector and scalar components. -/
def mk (x : V) (a : R) : SpinFactor R V B := (x, a)

@[simp] theorem mk_fst (x : V) (a : R) : (mk B x a).1 = x := rfl
@[simp] theorem mk_snd (x : V) (a : R) : (mk B x a).2 = a := rfl

instance : Mul (SpinFactor R V B) where
  mul z w := mk B (z.2 • w.1 + w.2 • z.1) (B z.1 w.1 + z.2 * w.2)

@[simp] theorem mul_fst (z w : SpinFactor R V B) :
    (z * w).1 = z.2 • w.1 + w.2 • z.1 := rfl

@[simp] theorem mul_snd (z w : SpinFactor R V B) :
    (z * w).2 = B z.1 w.1 + z.2 * w.2 := rfl

instance : One (SpinFactor R V B) := ⟨mk B 0 1⟩

@[simp] theorem one_fst : (1 : SpinFactor R V B).1 = 0 := rfl
@[simp] theorem one_snd : (1 : SpinFactor R V B).2 = 1 := rfl

instance : NonAssocRing (SpinFactor R V B) where
  left_distrib z w v := by ext <;> simp [smul_add, mul_add] <;> [module; ring]
  right_distrib z w v := by ext <;> simp [add_smul, map_add, add_mul] <;> [module; ring]
  zero_mul z := by ext <;> simp
  mul_zero z := by ext <;> simp
  one_mul z := by ext <;> simp
  mul_one z := by ext <;> simp

theorem mul_comm (hB : B.IsSymm) (z w : SpinFactor R V B) : z * w = w * z := by
  obtain ⟨x, a⟩ := z
  obtain ⟨y, b⟩ := w
  ext
  · simp [add_comm]
  · calc
      B x y + a * b = B y x + a * b := congrArg (fun t => t + a * b) (hB.eq x y)
      _ = B y x + b * a := by rw [_root_.mul_comm a b]
      _ = _ := rfl

instance : IsScalarTower R (SpinFactor R V B) (SpinFactor R V B) where
  smul_assoc r z w := by
    ext <;> simp [smul_add, smul_smul, smul_eq_mul] <;> ring

instance : SMulCommClass R (SpinFactor R V B) (SpinFactor R V B) where
  smul_comm r z w := by
    ext <;> simp [smul_add, smul_smul, smul_eq_mul] <;> ring

/-- A symmetric form gives the commutative Jordan algebra structure on the spin factor. -/
@[instance_reducible]
noncomputable def nonAssocCommRing (hB : B.IsSymm) : NonAssocCommRing (SpinFactor R V B) where
  __ := (inferInstance : NonAssocRing (SpinFactor R V B))
  mul_comm := mul_comm B hB

/-- The Jordan identity for the spin-factor product. -/
theorem isCommJordan (hB : B.IsSymm) :
    let _ : NonAssocCommRing (SpinFactor R V B) := nonAssocCommRing B hB
    IsCommJordan (SpinFactor R V B) := by
  let : NonAssocCommRing (SpinFactor R V B) := nonAssocCommRing B hB
  refine ⟨?_⟩
  intro z w
  obtain ⟨x, a⟩ := z
  obtain ⟨y, b⟩ := w
  have hxy : B x y = B y x := by simpa using hB.eq x y
  ext <;> simp [mul_fst, mul_snd, smul_eq_mul, hxy] <;> [module; ring]

/-- The rank-two determinant/norm form of a spin factor. -/
def determinant : QuadraticMap R (SpinFactor R V B) R :=
  QuadraticMap.sq.comp
    { toFun := fun z => z.2
      map_add' := add_snd B
      map_smul' := smul_snd B } -
  B.toQuadraticMap.comp
    { toFun := fun z => z.1
      map_add' := add_fst B
      map_smul' := smul_fst B }

@[simp] theorem determinant_apply (z : SpinFactor R V B) :
    determinant B z = z.2 * z.2 - B z.1 z.1 := by
  simp [determinant]

/-- The quadratic Cayley--Hamilton identity characteristic of rank-two spin factors. -/
theorem mul_self_sub_two_smul_snd_mul_add_determinant_smul_one
    (z : SpinFactor R V B) :
    z * z - (2 * z.2) • z + determinant B z • (1 : SpinFactor R V B) = 0 := by
  obtain ⟨x, a⟩ := z
  ext <;> simp [mul_fst, mul_snd, determinant_apply, smul_eq_mul] <;> [module; ring]

end SpinFactor

end JordanAlgebra
