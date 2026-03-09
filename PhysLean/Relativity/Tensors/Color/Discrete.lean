/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Mathlib.RepresentationTheory.Rep
/-!

# Discrete color category

-/

@[expose] public section

namespace IndexNotation
namespace OverColor
namespace Discrete

open CategoryTheory
open MonoidalCategory
open TensorProduct
variable {C k : Type} [CommRing k] {G : Type} [Group G]

variable (F F' : Discrete C ⥤ Rep k G) (η : F ⟶ F')
noncomputable section

/-- The functor taking `c` to `F c ⊗ F c`. -/
def pair : Discrete C ⥤ Rep k G := F ⊗ F

/-- The functor taking `c` to `F c ⊗ F (τ c)`. -/
def pairτ (τ : C → C) : Discrete C ⥤ Rep k G :=
  F ⊗ ((Discrete.functor (Discrete.mk ∘ τ) : Discrete C ⥤ Discrete C) ⋙ F)

lemma pairτ_tmul {c : C} (x : F.obj (Discrete.mk c))
    (y : ↑(((Action.functorCategoryEquivalence (ModuleCat k) (MonCat.of G)).symm.inverse.obj
    ((Discrete.functor (Discrete.mk ∘ τ) ⋙ F).obj { as := c })).obj PUnit.unit)) (h : c = c1) :
    ((pairτ F τ).map (Discrete.eqToHom h)).hom (x ⊗ₜ[k] y)= ((F.map (Discrete.eqToHom h)).hom x)
    ⊗ₜ[k] ((F.map (Discrete.eqToHom (by simp [h]))).hom y) := by
  rfl

/-- The functor taking `c` to `F (τ c) ⊗ F c`. -/
def τPair (τ : C → C) : Discrete C ⥤ Rep k G :=
  ((Discrete.functor (Discrete.mk ∘ τ) : Discrete C ⥤ Discrete C) ⋙ F) ⊗ F

end
end Discrete
end OverColor
end IndexNotation
