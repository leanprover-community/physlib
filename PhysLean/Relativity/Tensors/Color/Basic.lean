/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Mathlib.CategoryTheory.Core
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import PhysLean.Meta.TODO.Basic
/-!

# Color

In the context of tensors `Color` is defined as the type of indices of a tensor.
For example if `A_μ^ν` is a real Lorentz tensors, we say it has indices of color `[down, up]`.
For complex Lorentz Tensors there are six different colors, corresponding to the
up and down indices of the Lorentz group, the dotted and undotted Weyl fermion indices.

_Note if you only want to work with tensors, and not understand their implementation
you can safely ignore these files._

## Overview of directory

**This file**

Let `C` be the type of colors for a given species of tensor.
In this file we define the category `OverColor C`. The objects of `OverColor C`
correspond to allowed colorings of indices represented as a map `X → C` from a type `X` to `C`.
Usually `X` will be `Fin n` for some `n : ℕ`.
The morphisms of `OverColor C` correspond to color-preserving permutations of indices.

We also define here a symmetric-monoidal structure on `OverColor C`.

**Discrete**

The file `Discrete` contains some basic properties of the category `Discrete C`.

**Lift**

The file `Lift` we define the lift of a functor `F : Discrete C ⥤ Rep k G` to
a symmetric monoidal functor `OverColor C ⥤ Rep k G`, given by taking tensor products.

## References
- *Formalization of physics index notation in Lean 4*, Tooby-Smith.
<https://doi.org/10.48550/arXiv.2411.07667>.

-/

@[expose] public section

namespace IndexNotation
open CategoryTheory

/-- The core of the category of Types over C. -/
def OverColor (C : Type) := CategoryTheory.Core (CategoryTheory.Over C)

/-- The instance of `OverColor C` as a groupoid. -/
instance (C : Type) : Groupoid (OverColor C) := coreCategory

namespace OverColor

/-- Make an object of `OverColor C` from a map `X → C`. -/
def mk (f : X → C) : OverColor C := ⟨Over.mk f⟩

/-- The underlying morphism in the category of Types of a object `f` in `OverColor C`. -/
abbrev hom (f : OverColor C) := f.of.hom

/-- The underlying object in the category of Types of a object `f` in `OverColor C`. -/
abbrev left (f : OverColor C) := f.of.left

lemma mk_hom (f : X → C) : (mk f).hom = f := rfl

open MonoidalCategory

lemma mk_left (f : X → C) : (mk f).left = X := rfl

/-!

## Morphisms in the OverColor category.

-/

namespace Hom

variable {C : Type} {f g h : OverColor C}

/-- The underlying morphism in the category of Types of a morphism `m` in `OverColor C`. -/
abbrev _root_.CategoryTheory.CoreHom.hom (m : f ⟶ g) := m.iso.hom

/-- The underlying inverse-morphism in the category of Types of a morphism `m` in `OverColor C`. -/
abbrev _root_.CategoryTheory.CoreHom.inv (m : f ⟶ g) := m.iso.inv

lemma _root_.CategoryTheory.CoreHom.hom_inv_id (m : f ⟶ g) : m.iso.hom ≫ m.iso.inv = 𝟙 f.of :=
  m.iso.hom_inv_id

lemma _root_.CategoryTheory.CoreHom.inv_hom_id (m : f ⟶ g) : m.iso.inv ≫ m.iso.hom = 𝟙 g.of :=
  m.iso.inv_hom_id

/-- The inverse of a morphism in `OverColor C`. -/
abbrev _root_.CategoryTheory.CoreHom.symm (m : f ⟶ g) : g ⟶ f := ⟨m.iso.symm⟩

/-- If `m` and `n` are morphisms in `OverColor C`, they are equal if their underlying
  morphisms in `Over C` are equal. -/
lemma ext (m n : f ⟶ g) (h : m.hom = n.hom) : m = n := by
  have h1 := CategoryTheory.Iso.ext h
  rw [← CoreHom.ext_iff] at h1
  exact h1

lemma ext_iff (m n : f ⟶ g) : (∀ x, m.hom.left x = n.hom.left x) ↔ m = n := by
  refine Iff.intro (fun h => ?_) (fun h => ?_)
  · apply ext
    ext x
    exact h x
  · rw [h]
    exact fun x => rfl

/-- Given a hom in `OverColor C` the underlying equivalence between types. -/
def toEquiv (m : f ⟶ g) : f.left ≃ g.left where
  toFun := m.hom.left
  invFun := m.inv.left
  left_inv := by
    simpa only [Over.comp_left] using congrFun (congrArg (fun x => x.left) m.hom_inv_id)
  right_inv := by
    simpa only [Over.comp_left] using congrFun (congrArg (fun x => x.left) m.inv_hom_id)

/-- The equivalence of types underlying the identity morphism is the reflexive equivalence. -/
@[simp]
lemma toEquiv_id (f : OverColor C) : toEquiv (𝟙 f) = Equiv.refl f.left := by
  rfl

/-- The function `toEquiv` obeys compositions. -/
@[simp]
lemma toEquiv_comp (m : f ⟶ g) (n : g ⟶ h) : toEquiv (m ≫ n) = (toEquiv m).trans (toEquiv n) := by
  rfl

lemma toEquiv_symm_apply (m : f ⟶ g) (i : g.left) :
    f.hom ((toEquiv m).symm i) = g.hom i := by
  simpa [toEquiv, types_comp] using congrFun m.inv.w i

lemma toEquiv_comp_hom (m : f ⟶ g) : g.hom ∘ (toEquiv m) = f.hom := by
  ext x
  simpa [types_comp, toEquiv] using congrFun m.hom.w x

lemma toEquiv_comp_inv_apply (m : f ⟶ g) (i : g.left) :
    f.hom ((OverColor.Hom.toEquiv m).symm i) = g.hom i := by
  simpa [toEquiv, types_comp] using congrFun m.inv.w i

lemma toEquiv_comp_apply (m : f ⟶ g) (i : f.left) :
    f.hom i = g.hom ((toEquiv m) i) := by
  simpa [toEquiv, types_comp] using (congrFun m.hom.w i).symm

/-- Given a morphism in `OverColor C`, the corresponding isomorphism. -/
def toIso (m : f ⟶ g) : f ≅ g := {
  hom := m
  inv := m.symm
  hom_inv_id := CoreHom.ext_iff.mpr <| CategoryTheory.Iso.ext <| Over.OverMorphism.ext <|
      funext fun x => by
    simp only [CategoryStruct.comp, Iso.self_symm_id, Iso.refl_hom, Over.id_left, types_id_apply]
    rfl
  inv_hom_id := CoreHom.ext_iff.mpr <| CategoryTheory.Iso.ext <| Over.OverMorphism.ext <|
      funext fun x => by
    simp only [CategoryStruct.comp, Iso.symm_self_id, Iso.refl_hom, Over.id_left, types_id_apply]
    rfl}

@[simp]
lemma hom_comp (m : f ⟶ g) (n : g ⟶ h) : (m ≫ n).hom = m.hom ≫ n.hom := by rfl

end Hom

section monoidal

/-!

## The monoidal structure on `OverColor C`.

The category `OverColor C` can, through the disjoint union, be given the structure of a
symmetric monoidal category.

-/

/-- The category `OverColor C` carries an instance of a Monoidal category structure. -/
@[simps!]
instance (C : Type) : MonoidalCategoryStruct (OverColor C) where
  tensorObj f g := mk (Sum.elim f.hom g.hom)
  tensorUnit := mk Empty.elim
  whiskerLeft X Y1 Y2 m := ⟨Over.isoMk (Equiv.sumCongr (Equiv.refl X.left) (Hom.toEquiv m)).toIso
    (by
      ext x
      simp only [Functor.id_obj, mk, Functor.const_obj_obj, Over.mk_left, Equiv.toIso_hom,
        Over.mk_hom, types_comp_apply, Equiv.sumCongr_apply, Equiv.coe_refl]
      rw [Sum.elim_map, Hom.toEquiv_comp_hom]
      rfl)⟩
  whiskerRight m X := ⟨Over.isoMk (Equiv.sumCongr (Hom.toEquiv m) (Equiv.refl X.left)).toIso
    (by
      ext x
      simp only [Functor.id_obj, mk, Functor.const_obj_obj, Over.mk_left, Equiv.toIso_hom,
        Over.mk_hom, types_comp_apply, Equiv.sumCongr_apply, Equiv.coe_refl]
      rw [Sum.elim_map, Hom.toEquiv_comp_hom]
      rfl)⟩
  associator X Y Z := {
    hom := ⟨Over.isoMk (Equiv.sumAssoc X.left Y.left Z.left).toIso (by
      ext x
      match x with
      | Sum.inl (Sum.inl x) => rfl
      | Sum.inl (Sum.inr x) => rfl
      | Sum.inr x => rfl)⟩
    inv := ⟨(Over.isoMk (Equiv.sumAssoc X.left Y.left Z.left).toIso (by
      ext x
      match x with
      | Sum.inl (Sum.inl x) => rfl
      | Sum.inl (Sum.inr x) => rfl
      | Sum.inr x => rfl)).symm⟩
    hom_inv_id := CoreHom.ext_iff.mpr <| CategoryTheory.Iso.ext <| Over.OverMorphism.ext <|
        funext fun x => by
      match x with
      | Sum.inl (Sum.inl x) => rfl
      | Sum.inl (Sum.inr x) => rfl
      | Sum.inr x => rfl,
    inv_hom_id := by
      rw [CoreHom.ext_iff]
      apply CategoryTheory.Iso.ext
      simp only [Functor.id_obj, Hom.hom_comp]
      simp only [mk, Over.mk_left, CoreHom.hom, Iso.symm_hom, Iso.inv_hom_id]
      rfl}
  leftUnitor X := {
    hom := ⟨Over.isoMk (Equiv.emptySum Empty X.left).toIso (by
      simp only [OverColor.left, mk]
      aesop_cat)⟩
    inv := ⟨(Over.isoMk (Equiv.emptySum Empty X.left).toIso
      (by simp only [OverColor.left, mk]; aesop_cat)).symm⟩
    hom_inv_id := by
      rw [CoreHom.ext_iff]
      apply CategoryTheory.Iso.ext
      simp only [Functor.id_obj, Hom.hom_comp]
      simp only [mk, Over.mk_left, CoreHom.hom, Iso.symm_hom, Iso.hom_inv_id]
      rfl
    inv_hom_id := by
      rfl}
  rightUnitor X := {
    hom := ⟨Over.isoMk (Equiv.sumEmpty X.left Empty).toIso
      (by simp only [OverColor.left, mk]; aesop_cat)⟩
    inv := ⟨(Over.isoMk (Equiv.sumEmpty X.left Empty).toIso
      (by simp only [OverColor.left, mk]; aesop_cat)).symm⟩
    hom_inv_id := by
      rw [CoreHom.ext_iff]
      apply CategoryTheory.Iso.ext
      simp only [Functor.id_obj, Hom.hom_comp]
      simp only [mk, Over.mk_left, CoreHom.hom, Iso.symm_hom, Iso.hom_inv_id]
      rfl
    inv_hom_id := by
      rfl}

/-- The category `OverColor C` carries an instance of a Monoidal category. -/
instance (C : Type) : MonoidalCategory (OverColor C) where
    tensorHom_def f g := CoreHom.ext_iff.mpr <| CategoryTheory.Iso.ext <| Over.OverMorphism.ext <|
        funext fun x => rfl
    id_tensorHom_id X Y :=CoreHom.ext_iff.mpr <| CategoryTheory.Iso.ext <|
      (Iso.eq_inv_comp _).mp rfl
    tensorHom_comp_tensorHom f1 f2 g1 g2 := CoreHom.ext_iff.mpr <| CategoryTheory.Iso.ext <|
        Over.OverMorphism.ext <| funext fun x => by
      match x with
      | Sum.inl x => rfl
      | Sum.inr x => rfl
    whiskerLeft_id X Y := CoreHom.ext_iff.mpr <| CategoryTheory.Iso.ext <| Over.OverMorphism.ext
        <| funext fun x => by
      match x with
      | Sum.inl x => rfl
      | Sum.inr x => rfl
    id_whiskerRight X Y := CoreHom.ext_iff.mpr <| CategoryTheory.Iso.ext <| Over.OverMorphism.ext
        <| funext fun x => by
      match x with
      | Sum.inl x => rfl
      | Sum.inr x => rfl
    associator_naturality {X1 X2 X3 Y1 Y2 Y3} f1 f2 f3 :=
        CoreHom.ext_iff.mpr <| CategoryTheory.Iso.ext <| Over.OverMorphism.ext <|
          funext fun x => by
      match x with
      | Sum.inl (Sum.inl x) => rfl
      | Sum.inl (Sum.inr x) => rfl
      | Sum.inr x => rfl
    leftUnitor_naturality f :=
      CoreHom.ext_iff.mpr <| CategoryTheory.Iso.ext <| Over.OverMorphism.ext <|
        funext fun x => by
      match x with
      | Sum.inl x => exact Empty.elim x
      | Sum.inr x => rfl
    rightUnitor_naturality f :=
        CoreHom.ext_iff.mpr <| CategoryTheory.Iso.ext <| Over.OverMorphism.ext <|
          funext fun x => by
      match x with
      | Sum.inl x => rfl
      | Sum.inr x => exact Empty.elim x
    pentagon f g h i := CoreHom.ext_iff.mpr <| CategoryTheory.Iso.ext <|
        Over.OverMorphism.ext <| funext fun x => by
      match x with
      | Sum.inl (Sum.inl (Sum.inl x)) => rfl
      | Sum.inl (Sum.inl (Sum.inr x)) => rfl
      | Sum.inl (Sum.inr x) => rfl
      | Sum.inr x => rfl
    triangle f g := CoreHom.ext_iff.mpr <| CategoryTheory.Iso.ext <|
        Over.OverMorphism.ext <| funext fun x => by
      match x with
      | Sum.inl (Sum.inl x) => rfl
      | Sum.inl (Sum.inr x) => exact Empty.elim x
      | Sum.inr x => rfl

/-- The category `OverColor C` carries an instance of a braided category. -/
instance (C : Type) : BraidedCategory (OverColor C) where
  braiding f g := {
    hom := ⟨Over.isoMk (Equiv.sumComm f.left g.left).toIso
      (by simp only [OverColor.left]; aesop_cat)⟩
    inv := ⟨(Over.isoMk (Equiv.sumComm f.left g.left).toIso
      (by simp only [OverColor.left]; aesop_cat)).symm⟩
    hom_inv_id := CoreHom.ext_iff.mpr <| CategoryTheory.Iso.ext <|
        Over.OverMorphism.ext <| funext fun x => by
      match x with
      | Sum.inl x => rfl
      | Sum.inr x => rfl,
    inv_hom_id := CoreHom.ext_iff.mpr <| CategoryTheory.Iso.ext <|
        Over.OverMorphism.ext <| funext fun x => by
      match x with
      | Sum.inl x => rfl
      | Sum.inr x => rfl}
  braiding_naturality_right X Y1 Y2 f := CoreHom.ext_iff.mpr <|
      CategoryTheory.Iso.ext <| Over.OverMorphism.ext <| funext fun x => by
    match x with
    | Sum.inl x => rfl
    | Sum.inr x => rfl
  braiding_naturality_left X f := CoreHom.ext_iff.mpr <| CategoryTheory.Iso.ext
      <| Over.OverMorphism.ext <| funext fun x => by
    match x with
    | Sum.inl x => rfl
    | Sum.inr x => rfl
  hexagon_forward X1 X2 X3 := CoreHom.ext_iff.mpr <| CategoryTheory.Iso.ext <| Over.OverMorphism.ext
      <| funext fun x => by
    match x with
    | Sum.inl (Sum.inl x) => rfl
    | Sum.inl (Sum.inr x) => rfl
    | Sum.inr x => rfl
  hexagon_reverse X1 X2 X3 := CoreHom.ext_iff.mpr <| CategoryTheory.Iso.ext <| Over.OverMorphism.ext
      <| funext fun x => by
    match x with
    | Sum.inr (Sum.inl x) => rfl
    | Sum.inr (Sum.inr x) => rfl
    | Sum.inl x => rfl

/-- The category `OverColor C` carries an instance of a symmetric monoidal category. -/
instance (C : Type) : SymmetricCategory (OverColor C) where
  toBraidedCategory := instBraidedCategory C
  symmetry X Y := CoreHom.ext_iff.mpr <| CategoryTheory.Iso.ext <|
      Over.OverMorphism.ext <| funext fun x => by
    match x with
    | Sum.inl x => rfl
    | Sum.inr x => rfl

end monoidal

lemma Hom.fin_ext {n : ℕ} {f g : Fin n → C} (σ σ' : OverColor.mk f ⟶ OverColor.mk g)
    (h : ∀ (i : Fin n), σ.hom.left i = σ'.hom.left i) : σ = σ' := by
  apply Hom.ext
  ext i
  apply h

@[simp]
lemma β_hom_toEquiv (f : X → C) (g : Y → C) :
    Hom.toEquiv (β_ (OverColor.mk f) (OverColor.mk g)).hom = Equiv.sumComm X Y := by
  rfl

@[simp]
lemma β_inv_toEquiv (f : X → C) (g : Y → C) :
    Hom.toEquiv (β_ (OverColor.mk f) (OverColor.mk g)).inv = Equiv.sumComm Y X := by
  rfl

@[simp]
lemma whiskeringLeft_toEquiv (f : X → C) (g : Y → C) (h : Z → C)
    (σ : OverColor.mk f ⟶ OverColor.mk g) :
    Hom.toEquiv (OverColor.mk h ◁ σ) = (Equiv.refl Z).sumCongr (Hom.toEquiv σ) := by
  simp only [MonoidalCategoryStruct.whiskerLeft, mk_left, Functor.id_obj, mk_hom]
  rfl

@[simp]
lemma whiskeringRight_toEquiv (f : X → C) (g : Y → C) (h : Z → C)
    (σ : OverColor.mk f ⟶ OverColor.mk g) :
    Hom.toEquiv (σ ▷ OverColor.mk h) = (Hom.toEquiv σ).sumCongr (Equiv.refl Z) := by
  simp only [mk_left]
  rfl

@[simp]
lemma α_hom_toEquiv (f : X → C) (g : Y → C) (h : Z → C) :
    Hom.toEquiv (α_ (OverColor.mk f) (OverColor.mk g) (OverColor.mk h)).hom =
    Equiv.sumAssoc X Y Z := by
  rfl

@[simp]
lemma α_inv_toEquiv (f : X → C) (g : Y → C) (h : Z → C) :
    Hom.toEquiv (α_ (OverColor.mk f) (OverColor.mk g) (OverColor.mk h)).inv =
    (Equiv.sumAssoc X Y Z).symm := by
  rfl

/-!

## Isomorphisms.

-/

/-- The isomorphism between `c : X → C` and `c ∘ e.symm` as objects in `OverColor C` for an
  equivalence `e`. -/
def equivToIso {c : X → C} (e : X ≃ Y) : mk c ≅ mk (c ∘ e.symm) :=
  Hom.toIso ⟨Over.isoMk e.toIso ((Iso.eq_inv_comp e.toIso).mp rfl)⟩

@[simp]
lemma equivToIso_homToEquiv {c : X → C} (e : X ≃ Y) :
    Hom.toEquiv (equivToIso (c := c) e).hom = e := by
  rfl

@[simp]
lemma equivToIso_inv_homToEquiv {c : X → C} (e : X ≃ Y) :
    Hom.toEquiv (equivToIso (c := c) e).inv = e.symm := by
  rfl

/-- The homomorphism between `c : X → C` and `c ∘ e.symm` as objects in `OverColor C` for an
  equivalence `e`. -/
def equivToHom {c : X → C} (e : X ≃ Y) : mk c ⟶ mk (c ∘ e.symm) :=
  (equivToIso e).hom

/-- Given a map `X ⊕ Y → C`, the isomorphism `mk c ≅ mk (c ∘ Sum.inl) ⊗ mk (c ∘ Sum.inr)`. -/
def mkSum (c : X ⊕ Y → C) : mk c ≅ mk (c ∘ Sum.inl) ⊗ mk (c ∘ Sum.inr) :=
  Hom.toIso ⟨Over.isoMk (Equiv.refl _).toIso (by
    ext x
    match x with
    | Sum.inl x => rfl
    | Sum.inr x => rfl)⟩

@[simp]
lemma mkSum_homToEquiv {c : X ⊕ Y → C}:
    Hom.toEquiv (mkSum c).hom = (Equiv.refl _) := by
  rfl

@[simp]
lemma mkSum_inv_homToEquiv {c : X ⊕ Y → C}:
    Hom.toEquiv (mkSum c).inv = (Equiv.refl _) := by
  rfl

/-- The isomorphism between objects in `OverColor C` given equality of maps. -/
def mkIso {c1 c2 : X → C} (h : c1 = c2) : mk c1 ≅ mk c2 :=
  Hom.toIso ⟨Over.isoMk (Equiv.refl _).toIso (by
    subst h
    rfl)⟩

lemma mkIso_refl_hom {c : X → C} : (mkIso (by rfl : c =c)).hom = 𝟙 _ := by
  rw [mkIso]
  rfl

lemma mkIso_hom_hom_left {c1 c2 : X → C} (h : c1 = c2) : (mkIso h).hom.hom.left =
    (Equiv.refl X).toFun := by
  rw [mkIso]
  rfl

@[simp]
lemma mkIso_hom_hom_left_apply {c1 c2 : X → C} (h : c1 = c2) (x : X) :
    (mkIso h).hom.hom.left x = x := by
  rw [mkIso_hom_hom_left]
  rfl

@[simp]
lemma equivToIso_mkIso_hom {c1 c2 : X → C} (h : c1 = c2) :
    Hom.toEquiv (mkIso h).hom = Equiv.refl _ := by
  rfl

@[simp]
lemma equivToIso_mkIso_inv {c1 c2 : X → C} (h : c1 = c2) :
    Hom.toEquiv (mkIso h).inv = Equiv.refl _ := by
  rfl

/-- The morphism from `mk c` to `mk c1` obtained by an equivalence and
  an equality lemma. -/
def equivToHomEq {c : X → C} {c1 : Y → C} (e : X ≃ Y)
    (h : ∀ x, c1 x = (c ∘ e.symm) x := by simp; decide) : mk c ⟶ mk c1 :=
  (equivToHom e) ≫ (mkIso (funext fun x => (h x).symm)).hom

@[simp]
lemma equivToHomEq_hom_left {c : X → C} {c1 : Y → C} (e : X ≃ Y)
    (h : ∀ x, c1 x = (c ∘ e.symm) x) : (equivToHomEq e h).hom.left =
    e.toFun := by
  rfl

@[simp]
lemma equivToHomEq_toEquiv {c : X → C} {c1 : Y → C} (e : X ≃ Y)
    (h : ∀ x, c1 x = (c ∘ e.symm) x) :
    Hom.toEquiv (equivToHomEq e h) = e := by
  rfl

end OverColor

end IndexNotation
