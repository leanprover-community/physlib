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

# Jordan homomorphisms

Jordan homomorphisms: unital real-linear maps between Jordan algebras preserving the product.

## i. Overview

A Jordan homomorphism between unital real Jordan algebras is a real-linear unital map preserving the
Jordan product.

## ii. Key results

- `JordanAlgebra.JordanHom` : Jordan homomorphisms.
- `JordanAlgebra.JordanHom.comp` : composition.
- `JordanAlgebra.JordanHom.id` : the identity Jordan homomorphism.
- `JordanAlgebra.JordanHom.comp_assoc` : composition is associative.

## iii. Table of contents

- A. Jordan homomorphisms
- B. Identity and composition

## iv. References

* None.

-/

@[expose] public section

namespace ProbabilisticTheory

namespace JordanAlgebra

variable {E F G : Type*} [NonAssocCommRing E] [Module ℝ E]
  [NonAssocCommRing F] [Module ℝ F] [NonAssocCommRing G] [Module ℝ G]

/-!

## A. Jordan homomorphisms

-/

/-- A unital real-linear map preserving the Jordan product. -/
structure JordanHom (E F : Type*) [NonAssocCommRing E] [Module ℝ E]
    [NonAssocCommRing F] [Module ℝ F] extends E →ₗ[ℝ] F where
  map_one' : toLinearMap 1 = 1
  map_mul' : ∀ x y, toLinearMap (x * y) = toLinearMap x * toLinearMap y

namespace JordanHom

instance : CoeFun (JordanHom E F) fun _ => E → F := ⟨fun f => f.toLinearMap⟩

@[ext]
lemma ext {f g : JordanHom E F} (h : ∀ x, f x = g x) : f = g := by
  rcases f with ⟨f, hf₁, hf₂⟩
  rcases g with ⟨g, hg₁, hg₂⟩
  dsimp at h
  have hfg : f = g := LinearMap.ext h
  subst g
  rfl

@[simp]
lemma map_zero (f : JordanHom E F) : f 0 = 0 := f.toLinearMap.map_zero

@[simp]
lemma map_add (f : JordanHom E F) (x y : E) : f (x + y) = f x + f y :=
  f.toLinearMap.map_add x y

lemma map_smul (f : JordanHom E F) (r : ℝ) (x : E) : f (r • x) = r • f x :=
  f.toLinearMap.map_smul r x

@[simp]
lemma map_one (f : JordanHom E F) : f 1 = 1 := f.map_one'

@[simp]
lemma map_mul (f : JordanHom E F) (x y : E) : f (x * y) = f x * f y :=
  f.map_mul' x y

/-!

## B. Identity and composition

-/

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
lemma id_apply (x : E) : id x = x := rfl

@[simp]
lemma comp_apply (g : JordanHom F G) (f : JordanHom E F) (x : E) :
    g.comp f x = g (f x) := rfl

@[simp]
lemma id_comp (f : JordanHom E F) : (id : JordanHom F F).comp f = f := by
  ext x
  rfl

@[simp]
lemma comp_id (f : JordanHom E F) : f.comp (id : JordanHom E E) = f := by
  ext x
  rfl

lemma comp_assoc (h : JordanHom G E) (g : JordanHom F G) (f : JordanHom E F) :
    (h.comp g).comp f = h.comp (g.comp f) := by
  ext x
  rfl

end JordanHom

end JordanAlgebra

end ProbabilisticTheory
