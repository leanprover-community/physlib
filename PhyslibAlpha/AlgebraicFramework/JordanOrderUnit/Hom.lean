/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license and described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Mathlib.Algebra.Jordan.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Module.LinearMap.Basic

/-!
# Unital real Jordan homomorphisms

`JordanHom` is the minimal bundled map between unital real Jordan algebras: it is real-linear,
unital, and preserves the Jordan product.  It has no order, norm, completeness, Cstar, or
specialness requirement.  In particular it is the correct language for the inclusion of a
generated Jordan fragment and for the eventual local associative-envelope theorem.
-/

@[expose] public section

namespace JordanAlgebra

variable {E F G : Type*} [NonAssocCommRing E] [Module ℝ E]
  [NonAssocCommRing F] [Module ℝ F] [NonAssocCommRing G] [Module ℝ G]

/-- A unital real-linear map preserving the Jordan product. -/
structure JordanHom (E F : Type*) [NonAssocCommRing E] [Module ℝ E]
    [NonAssocCommRing F] [Module ℝ F] extends E →ₗ[ℝ] F where
  map_one' : toLinearMap 1 = 1
  map_mul' : ∀ x y, toLinearMap (x * y) = toLinearMap x * toLinearMap y

namespace JordanHom

instance : CoeFun (JordanHom E F) fun _ => E → F := ⟨fun f => f.toLinearMap⟩

@[ext]
theorem ext {f g : JordanHom E F} (h : ∀ x, f x = g x) : f = g := by
  rcases f with ⟨f, hf₁, hf₂⟩
  rcases g with ⟨g, hg₁, hg₂⟩
  dsimp at h
  have hfg : f = g := LinearMap.ext h
  subst g
  rfl

@[simp]
theorem map_zero (f : JordanHom E F) : f 0 = 0 := f.toLinearMap.map_zero

@[simp]
theorem map_add (f : JordanHom E F) (x y : E) : f (x + y) = f x + f y :=
  f.toLinearMap.map_add x y

theorem map_smul (f : JordanHom E F) (r : ℝ) (x : E) : f (r • x) = r • f x :=
  f.toLinearMap.map_smul r x

@[simp]
theorem map_one (f : JordanHom E F) : f 1 = 1 := f.map_one'

@[simp]
theorem map_mul (f : JordanHom E F) (x y : E) : f (x * y) = f x * f y :=
  f.map_mul' x y

/-- The identity Jordan homomorphism. -/
def id : JordanHom E E where
  toLinearMap := LinearMap.id
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Composition of unital real Jordan homomorphisms. -/
def comp (g : JordanHom F G) (f : JordanHom E F) : JordanHom E G where
  toLinearMap := g.toLinearMap.comp f.toLinearMap
  map_one' := by simp
  map_mul' x y := by simp

@[simp]
theorem id_apply (x : E) : id x = x := rfl

@[simp]
theorem comp_apply (g : JordanHom F G) (f : JordanHom E F) (x : E) :
    g.comp f x = g (f x) := rfl

@[simp]
theorem id_comp (f : JordanHom E F) : (id : JordanHom F F).comp f = f := by
  ext x
  rfl

@[simp]
theorem comp_id (f : JordanHom E F) : f.comp (id : JordanHom E E) = f := by
  ext x
  rfl

theorem comp_assoc (h : JordanHom G E) (g : JordanHom F G) (f : JordanHom E F) :
    (h.comp g).comp f = h.comp (g.comp f) := by
  ext x
  rfl

end JordanHom

end JordanAlgebra
